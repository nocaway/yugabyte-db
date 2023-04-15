/*-------------------------------------------------------------------------
 *
 * copy.c
 *		Implements the COPY utility command
 *
 * Portions Copyright (c) 1996-2022, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/commands/copy.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <ctype.h>
#include <unistd.h>
#include <sys/stat.h>

#include "access/sysattr.h"
#include "access/table.h"
#include "access/xact.h"
#include "catalog/pg_authid.h"
#include "commands/copy.h"
#include "commands/defrem.h"
#include "executor/executor.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "optimizer/optimizer.h"
#include "parser/parse_coerce.h"
#include "parser/parse_collate.h"
#include "parser/parse_expr.h"
#include "parser/parse_relation.h"
#include "rewrite/rewriteHandler.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/rls.h"

/* Yugabyte includes */
#include "pg_yb_utils.h"
#include "commands/progress.h"
#include "commands/trigger.h"
#include "executor/execPartition.h"
#include "executor/ybcModifyTable.h"
#include "port/pg_bswap.h"
#include "pgstat.h"

int yb_default_copy_from_rows_per_transaction = DEFAULT_BATCH_ROWS_PER_TRANSACTION;

/*
 *	 DoCopy executes the SQL COPY statement
 *
 * Either unload or reload contents of table <relation>, depending on <from>.
 * (<from> = true means we are inserting into the table.)  In the "TO" case
 * we also support copying the output of an arbitrary SELECT, INSERT, UPDATE
 * or DELETE query.
 *
 * If <pipe> is false, transfer is between the table and the file named
 * <filename>.  Otherwise, transfer is between the table and our regular
 * input/output stream. The latter could be either stdin/stdout or a
 * socket, depending on whether we're running under Postmaster control.
 *
 * Do not allow a Postgres user without the 'pg_read_server_files' or
 * 'pg_write_server_files' role to read from or write to a file.
 *
 * Do not allow the copy if user doesn't have proper permission to access
 * the table or the specifically requested columns.
 */
void
DoCopy(ParseState *pstate, const CopyStmt *stmt,
	   int stmt_location, int stmt_len,
	   uint64 *processed)
{
	bool		is_from = stmt->is_from;
	bool		pipe = (stmt->filename == NULL);
	Relation	rel;
	Oid			relid;
	RawStmt    *query = NULL;
	Node	   *whereClause = NULL;

	YBCheckServerAccessIsAllowed();

	if (!pipe)
	{
		if (stmt->is_program)
		{
			if (!has_privs_of_role(GetUserId(), ROLE_PG_EXECUTE_SERVER_PROGRAM))
				ereport(ERROR,
						(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
						 errmsg("must be superuser or have privileges of the pg_execute_server_program role to COPY to or from an external program"),
						 errhint("Anyone can COPY to stdout or from stdin. "
								 "psql's \\copy command also works for anyone.")));
		}
		else
		{
			if (is_from && !has_privs_of_role(GetUserId(), ROLE_PG_READ_SERVER_FILES))
				ereport(ERROR,
						(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
						 errmsg("must be superuser or have privileges of the pg_read_server_files role to COPY from a file"),
						 errhint("Anyone can COPY to stdout or from stdin. "
								 "psql's \\copy command also works for anyone.")));

			if (!is_from && !has_privs_of_role(GetUserId(), ROLE_PG_WRITE_SERVER_FILES))
				ereport(ERROR,
						(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
						 errmsg("must be superuser or have privileges of the pg_write_server_files role to COPY to a file"),
						 errhint("Anyone can COPY to stdout or from stdin. "
								 "psql's \\copy command also works for anyone.")));
		}
	}

	if (stmt->relation)
	{
		LOCKMODE	lockmode = is_from ? RowExclusiveLock : AccessShareLock;
		ParseNamespaceItem *nsitem;
		RangeTblEntry *rte;
		TupleDesc	tupDesc;
		List	   *attnums;
		ListCell   *cur;

		Assert(!stmt->query);

		/* Open and lock the relation, using the appropriate lock type. */
		rel = table_openrv(stmt->relation, lockmode);

		if (rel->rd_rel->relpersistence == RELPERSISTENCE_TEMP &&
				IsYugaByteEnabled()) {
			SetTxnWithPGRel();
		}

		relid = RelationGetRelid(rel);

		nsitem = addRangeTableEntryForRelation(pstate, rel, lockmode,
											   NULL, false, false);
		rte = nsitem->p_rte;
		rte->requiredPerms = (is_from ? ACL_INSERT : ACL_SELECT);

		if (stmt->whereClause)
		{
			/* add nsitem to query namespace */
			addNSItemToQuery(pstate, nsitem, false, true, true);

			/* Transform the raw expression tree */
			whereClause = transformExpr(pstate, stmt->whereClause, EXPR_KIND_COPY_WHERE);

			/* Make sure it yields a boolean result. */
			whereClause = coerce_to_boolean(pstate, whereClause, "WHERE");

			/* we have to fix its collations too */
			assign_expr_collations(pstate, whereClause);

			whereClause = eval_const_expressions(NULL, whereClause);

			whereClause = (Node *) canonicalize_qual((Expr *) whereClause, false);
			whereClause = (Node *) make_ands_implicit((Expr *) whereClause);
		}

		tupDesc = RelationGetDescr(rel);
		attnums = CopyGetAttnums(tupDesc, rel, stmt->attlist);
		foreach(cur, attnums)
		{
			int attno = lfirst_int(cur) - YBGetFirstLowInvalidAttributeNumber(rel);

			if (is_from)
				rte->insertedCols = bms_add_member(rte->insertedCols, attno);
			else
				rte->selectedCols = bms_add_member(rte->selectedCols, attno);
		}
		ExecCheckRTPerms(pstate->p_rtable, true);

		/*
		 * Permission check for row security policies.
		 *
		 * check_enable_rls will ereport(ERROR) if the user has requested
		 * something invalid and will otherwise indicate if we should enable
		 * RLS (returns RLS_ENABLED) or not for this COPY statement.
		 *
		 * If the relation has a row security policy and we are to apply it
		 * then perform a "query" copy and allow the normal query processing
		 * to handle the policies.
		 *
		 * If RLS is not enabled for this, then just fall through to the
		 * normal non-filtering relation handling.
		 */
		if (check_enable_rls(rte->relid, InvalidOid, false) == RLS_ENABLED)
		{
			SelectStmt *select;
			ColumnRef  *cr;
			ResTarget  *target;
			RangeVar   *from;
			List	   *targetList = NIL;

			if (is_from)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("COPY FROM not supported with row-level security"),
						 errhint("Use INSERT statements instead.")));

			/*
			 * Build target list
			 *
			 * If no columns are specified in the attribute list of the COPY
			 * command, then the target list is 'all' columns. Therefore, '*'
			 * should be used as the target list for the resulting SELECT
			 * statement.
			 *
			 * In the case that columns are specified in the attribute list,
			 * create a ColumnRef and ResTarget for each column and add them
			 * to the target list for the resulting SELECT statement.
			 */
			if (!stmt->attlist)
			{
				cr = makeNode(ColumnRef);
				cr->fields = list_make1(makeNode(A_Star));
				cr->location = -1;

				target = makeNode(ResTarget);
				target->name = NULL;
				target->indirection = NIL;
				target->val = (Node *) cr;
				target->location = -1;

				targetList = list_make1(target);
			}
			else
			{
				ListCell   *lc;

				foreach(lc, stmt->attlist)
				{
					/*
					 * Build the ColumnRef for each column.  The ColumnRef
					 * 'fields' property is a String node that corresponds to
					 * the column name respectively.
					 */
					cr = makeNode(ColumnRef);
					cr->fields = list_make1(lfirst(lc));
					cr->location = -1;

					/* Build the ResTarget and add the ColumnRef to it. */
					target = makeNode(ResTarget);
					target->name = NULL;
					target->indirection = NIL;
					target->val = (Node *) cr;
					target->location = -1;

					/* Add each column to the SELECT statement's target list */
					targetList = lappend(targetList, target);
				}
			}

			/*
			 * Build RangeVar for from clause, fully qualified based on the
			 * relation which we have opened and locked.
			 */
			from = makeRangeVar(get_namespace_name(RelationGetNamespace(rel)),
								pstrdup(RelationGetRelationName(rel)),
								-1);

			/* Build query */
			select = makeNode(SelectStmt);
			select->targetList = targetList;
			select->fromClause = list_make1(from);

			query = makeNode(RawStmt);
			query->stmt = (Node *) select;
			query->stmt_location = stmt_location;
			query->stmt_len = stmt_len;

			/*
			 * Close the relation for now, but keep the lock on it to prevent
			 * changes between now and when we start the query-based COPY.
			 *
			 * We'll reopen it later as part of the query-based COPY.
			 */
			table_close(rel, NoLock);
			rel = NULL;
		}
	}
	else
	{
		Assert(stmt->query);

		/* MERGE is allowed by parser, but unimplemented. Reject for now */
		if (IsA(stmt->query, MergeStmt))
			ereport(ERROR,
					errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("MERGE not supported in COPY"));

		query = makeNode(RawStmt);
		query->stmt = stmt->query;
		query->stmt_location = stmt_location;
		query->stmt_len = stmt_len;

		relid = InvalidOid;
		rel = NULL;
	}

	if (is_from)
	{
		CopyFromState cstate;

		Assert(rel);

		/* check read-only transaction and parallel mode */
		if (XactReadOnly && !rel->rd_islocaltemp)
			PreventCommandIfReadOnly("COPY FROM");

		cstate = BeginCopyFrom(pstate, rel, whereClause,
							   stmt->filename, stmt->is_program,
							   NULL, stmt->attlist, stmt->options);
		*processed = CopyFrom(cstate);	/* copy from file to database */
		EndCopyFrom(cstate);
	}
	else
	{
		CopyToState cstate;

		cstate = BeginCopyTo(pstate, rel, query, relid,
							 stmt->filename, stmt->is_program,
							 stmt->attlist, stmt->options);
		*processed = DoCopyTo(cstate);	/* copy from database to file */
		EndCopyTo(cstate);
	}

	if (rel != NULL)
		table_close(rel, NoLock);
}

/*
 * Extract a CopyHeaderChoice value from a DefElem.  This is like
 * defGetBoolean() but also accepts the special value "match".
 */
static CopyHeaderChoice
defGetCopyHeaderChoice(DefElem *def, bool is_from)
{
	/*
	 * If no parameter given, assume "true" is meant.
	 */
	if (def->arg == NULL)
		return COPY_HEADER_TRUE;

	/*
	 * Allow 0, 1, "true", "false", "on", "off", or "match".
	 */
	switch (nodeTag(def->arg))
	{
		case T_Integer:
			switch (intVal(def->arg))
			{
				case 0:
					return COPY_HEADER_FALSE;
				case 1:
					return COPY_HEADER_TRUE;
				default:
					/* otherwise, error out below */
					break;
			}
			break;
		default:
			{
				char	   *sval = defGetString(def);

				/*
				 * The set of strings accepted here should match up with the
				 * grammar's opt_boolean_or_string production.
				 */
				if (pg_strcasecmp(sval, "true") == 0)
					return COPY_HEADER_TRUE;
				if (pg_strcasecmp(sval, "false") == 0)
					return COPY_HEADER_FALSE;
				if (pg_strcasecmp(sval, "on") == 0)
					return COPY_HEADER_TRUE;
				if (pg_strcasecmp(sval, "off") == 0)
					return COPY_HEADER_FALSE;
				if (pg_strcasecmp(sval, "match") == 0)
				{
					if (!is_from)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("cannot use \"%s\" with HEADER in COPY TO",
										sval)));
					return COPY_HEADER_MATCH;
				}
			}
			break;
	}
	ereport(ERROR,
			(errcode(ERRCODE_SYNTAX_ERROR),
			 errmsg("%s requires a Boolean value or \"match\"",
					def->defname)));
	return COPY_HEADER_FALSE;	/* keep compiler quiet */
}

/*
 * Process the statement option list for COPY.
 *
 * Scan the options list (a list of DefElem) and transpose the information
 * into *opts_out, applying appropriate error checking.
 *
 * If 'opts_out' is not NULL, it is assumed to be filled with zeroes initially.
 *
 * This is exported so that external users of the COPY API can sanity-check
 * a list of options.  In that usage, 'opts_out' can be passed as NULL and
 * the collected data is just leaked until GetCurrentMemoryContext() is reset.
 *
 * Note that additional checking, such as whether column names listed in FORCE
 * QUOTE actually exist, has to be applied later.  This just checks for
 * self-consistency of the options list.
 */
void
ProcessCopyOptions(ParseState *pstate,
				   CopyFormatOptions *opts_out,
				   bool is_from,
				   List *options)
{
	bool		format_specified = false;
	bool		freeze_specified = false;
	bool		header_specified = false;
	ListCell   *option;

	/* Support external use for option sanity checking */
	if (opts_out == NULL)
		opts_out = (CopyFormatOptions *) palloc0(sizeof(CopyFormatOptions));

	opts_out->file_encoding = -1;

	/* Yugabyte options */
	opts_out->batch_size = -1;
	opts_out->num_initial_skipped_rows = 0;
	opts_out->disable_fk_check = false;
	opts_out->on_conflict_action = ONCONFLICT_NONE;

	/* Extract options from the statement node tree */
	foreach(option, options)
	{
		DefElem    *defel = lfirst_node(DefElem, option);

		if (strcmp(defel->defname, "format") == 0)
		{
			char	   *fmt = defGetString(defel);

			if (format_specified)
				errorConflictingDefElem(defel, pstate);
			format_specified = true;
			if (strcmp(fmt, "text") == 0)
				 /* default format */ ;
			else if (strcmp(fmt, "csv") == 0)
				opts_out->csv_mode = true;
			else if (strcmp(fmt, "binary") == 0)
				opts_out->binary = true;
			else
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("COPY format \"%s\" not recognized", fmt),
						 parser_errposition(pstate, defel->location)));
		}
		else if (strcmp(defel->defname, "freeze") == 0)
		{
			if (freeze_specified)
				errorConflictingDefElem(defel, pstate);
			freeze_specified = true;
			opts_out->freeze = defGetBoolean(defel);
		}
		else if (strcmp(defel->defname, "delimiter") == 0)
		{
			if (opts_out->delim)
				errorConflictingDefElem(defel, pstate);
			opts_out->delim = defGetString(defel);
		}
		else if (strcmp(defel->defname, "rows_per_transaction") == 0)
		{
			int rows = defGetInt32(defel);
			if (rows >= 0)
				opts_out->batch_size = rows;
			else
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("argument to option \"%s\" must be a positive integer", defel->defname),
						 parser_errposition(pstate, defel->location)));
		}
		else if (strcmp(defel->defname, "skip") == 0)
		{
			int64_t num_initial_skipped_rows = defGetInt64(defel);
			if (num_initial_skipped_rows >= 0)
				opts_out->num_initial_skipped_rows = num_initial_skipped_rows;
			else
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("argument to option \"%s\" must be a nonnegative integer", defel->defname),
						 parser_errposition(pstate, defel->location)));
		}
		else if (strcmp(defel->defname, "disable_fk_check") == 0)
			opts_out->disable_fk_check = true;
		else if (strcmp(defel->defname, "replace") == 0)
			opts_out->on_conflict_action = ONCONFLICT_YB_REPLACE;
		else if (strcmp(defel->defname, "null") == 0)
		{
			if (opts_out->null_print)
				errorConflictingDefElem(defel, pstate);
			opts_out->null_print = defGetString(defel);
		}
		else if (strcmp(defel->defname, "header") == 0)
		{
			if (header_specified)
				errorConflictingDefElem(defel, pstate);
			header_specified = true;
			opts_out->header_line = defGetCopyHeaderChoice(defel, is_from);
		}
		else if (strcmp(defel->defname, "quote") == 0)
		{
			if (opts_out->quote)
				errorConflictingDefElem(defel, pstate);
			opts_out->quote = defGetString(defel);
		}
		else if (strcmp(defel->defname, "escape") == 0)
		{
			if (opts_out->escape)
				errorConflictingDefElem(defel, pstate);
			opts_out->escape = defGetString(defel);
		}
		else if (strcmp(defel->defname, "force_quote") == 0)
		{
			if (opts_out->force_quote || opts_out->force_quote_all)
				errorConflictingDefElem(defel, pstate);
			if (defel->arg && IsA(defel->arg, A_Star))
				opts_out->force_quote_all = true;
			else if (defel->arg && IsA(defel->arg, List))
				opts_out->force_quote = castNode(List, defel->arg);
			else
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("argument to option \"%s\" must be a list of column names",
								defel->defname),
						 parser_errposition(pstate, defel->location)));
		}
		else if (strcmp(defel->defname, "force_not_null") == 0)
		{
			if (opts_out->force_notnull)
				errorConflictingDefElem(defel, pstate);
			if (defel->arg && IsA(defel->arg, List))
				opts_out->force_notnull = castNode(List, defel->arg);
			else
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("argument to option \"%s\" must be a list of column names",
								defel->defname),
						 parser_errposition(pstate, defel->location)));
		}
		else if (strcmp(defel->defname, "force_null") == 0)
		{
			if (opts_out->force_null)
				errorConflictingDefElem(defel, pstate);
			if (defel->arg && IsA(defel->arg, List))
				opts_out->force_null = castNode(List, defel->arg);
			else
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("argument to option \"%s\" must be a list of column names",
								defel->defname),
						 parser_errposition(pstate, defel->location)));
		}
		else if (strcmp(defel->defname, "convert_selectively") == 0)
		{
			/*
			 * Undocumented, not-accessible-from-SQL option: convert only the
			 * named columns to binary form, storing the rest as NULLs. It's
			 * allowed for the column list to be NIL.
			 */
			if (opts_out->convert_selectively)
				errorConflictingDefElem(defel, pstate);
			opts_out->convert_selectively = true;
			if (defel->arg == NULL || IsA(defel->arg, List))
				opts_out->convert_select = castNode(List, defel->arg);
			else
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("argument to option \"%s\" must be a list of column names",
								defel->defname),
						 parser_errposition(pstate, defel->location)));
		}
		else if (strcmp(defel->defname, "encoding") == 0)
		{
			if (opts_out->file_encoding >= 0)
				errorConflictingDefElem(defel, pstate);
			opts_out->file_encoding = pg_char_to_encoding(defGetString(defel));
			if (opts_out->file_encoding < 0)
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
						 errmsg("argument to option \"%s\" must be a valid encoding name",
								defel->defname),
						 parser_errposition(pstate, defel->location)));
		}
		else
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("option \"%s\" not recognized",
							defel->defname),
					 parser_errposition(pstate, defel->location)));
	}

	/*
	 * Check for incompatible options (must do these two before inserting
	 * defaults)
	 */
	if (opts_out->binary && opts_out->delim)
		ereport(ERROR,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("cannot specify DELIMITER in BINARY mode")));

	if (opts_out->binary && opts_out->null_print)
		ereport(ERROR,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("cannot specify NULL in BINARY mode")));

	/* Set defaults for omitted options */
	if (!opts_out->delim)
		opts_out->delim = opts_out->csv_mode ? "," : "\t";

	if (!opts_out->null_print)
		opts_out->null_print = opts_out->csv_mode ? "" : "\\N";
	opts_out->null_print_len = strlen(opts_out->null_print);

	if (opts_out->csv_mode)
	{
		if (!opts_out->quote)
			opts_out->quote = "\"";
		if (!opts_out->escape)
			opts_out->escape = opts_out->quote;
	}

	/* Only single-byte delimiter strings are supported. */
	if (strlen(opts_out->delim) != 1)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY delimiter must be a single one-byte character")));

	/* Disallow end-of-line characters */
	if (strchr(opts_out->delim, '\r') != NULL ||
		strchr(opts_out->delim, '\n') != NULL)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("COPY delimiter cannot be newline or carriage return")));

	if (strchr(opts_out->null_print, '\r') != NULL ||
		strchr(opts_out->null_print, '\n') != NULL)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("COPY null representation cannot use newline or carriage return")));

	/*
	 * Disallow unsafe delimiter characters in non-CSV mode.  We can't allow
	 * backslash because it would be ambiguous.  We can't allow the other
	 * cases because data characters matching the delimiter must be
	 * backslashed, and certain backslash combinations are interpreted
	 * non-literally by COPY IN.  Disallowing all lower case ASCII letters is
	 * more than strictly necessary, but seems best for consistency and
	 * future-proofing.  Likewise we disallow all digits though only octal
	 * digits are actually dangerous.
	 */
	if (!opts_out->csv_mode &&
		strchr("\\.abcdefghijklmnopqrstuvwxyz0123456789",
			   opts_out->delim[0]) != NULL)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("COPY delimiter cannot be \"%s\"", opts_out->delim)));

	/* Check header */
	if (opts_out->binary && opts_out->header_line)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot specify HEADER in BINARY mode")));

	/* Check quote */
	if (!opts_out->csv_mode && opts_out->quote != NULL)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY quote available only in CSV mode")));

	if (opts_out->csv_mode && strlen(opts_out->quote) != 1)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY quote must be a single one-byte character")));

	if (opts_out->csv_mode && opts_out->delim[0] == opts_out->quote[0])
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("COPY delimiter and quote must be different")));

	/* Check escape */
	if (!opts_out->csv_mode && opts_out->escape != NULL)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY escape available only in CSV mode")));

	if (opts_out->csv_mode && strlen(opts_out->escape) != 1)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY escape must be a single one-byte character")));

	/* Check force_quote */
	if (!opts_out->csv_mode && (opts_out->force_quote || opts_out->force_quote_all))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY force quote available only in CSV mode")));
	if ((opts_out->force_quote || opts_out->force_quote_all) && is_from)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY force quote only available using COPY TO")));

	/* Check force_notnull */
	if (!opts_out->csv_mode && opts_out->force_notnull != NIL)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY force not null available only in CSV mode")));
	if (opts_out->force_notnull != NIL && !is_from)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY force not null only available using COPY FROM")));

	/* Check force_null */
	if (!opts_out->csv_mode && opts_out->force_null != NIL)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY force null available only in CSV mode")));

	if (opts_out->force_null != NIL && !is_from)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY force null only available using COPY FROM")));

	/* Don't allow the delimiter to appear in the null string. */
	if (strchr(opts_out->null_print, opts_out->delim[0]) != NULL)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("COPY delimiter must not appear in the NULL specification")));

	/* Don't allow the CSV quote char to appear in the null string. */
	if (opts_out->csv_mode &&
		strchr(opts_out->null_print, opts_out->quote[0]) != NULL)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("CSV quote character must not appear in the NULL specification")));
}

/*
 * CopyGetAttnums - build an integer list of attnums to be copied
 *
 * The input attnamelist is either the user-specified column list,
 * or NIL if there was none (in which case we want all the non-dropped
 * columns).
 *
 * We don't include generated columns in the generated full list and we don't
 * allow them to be specified explicitly.  They don't make sense for COPY
 * FROM, but we could possibly allow them for COPY TO.  But this way it's at
 * least ensured that whatever we copy out can be copied back in.
 *
 * rel can be NULL ... it's only used for error reports.
 */
List *
CopyGetAttnums(TupleDesc tupDesc, Relation rel, List *attnamelist)
{
	List	   *attnums = NIL;

	if (attnamelist == NIL)
	{
		/* Generate default column list */
		int			attr_count = tupDesc->natts;
		int			i;

		for (i = 0; i < attr_count; i++)
		{
			if (TupleDescAttr(tupDesc, i)->attisdropped)
				continue;
			if (TupleDescAttr(tupDesc, i)->attgenerated)
				continue;
			attnums = lappend_int(attnums, i + 1);
		}
	}
<<<<<<< copy.c

	/* Convert FORCE_NOT_NULL name list to per-column flags, check validity */
	cstate->force_notnull_flags = (bool *) palloc0(num_phys_attrs * sizeof(bool));
	if (cstate->force_notnull)
	{
		List	   *attnums;
		ListCell   *cur;

		attnums = CopyGetAttnums(tupDesc, cstate->rel, cstate->force_notnull);

		foreach(cur, attnums)
		{
			int			attnum = lfirst_int(cur);
			Form_pg_attribute attr = TupleDescAttr(tupDesc, attnum - 1);

			if (!list_member_int(cstate->attnumlist, attnum))
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
						 errmsg("FORCE_NOT_NULL column \"%s\" not referenced by COPY",
								NameStr(attr->attname))));
			cstate->force_notnull_flags[attnum - 1] = true;
		}
	}

	/* Convert FORCE_NULL name list to per-column flags, check validity */
	cstate->force_null_flags = (bool *) palloc0(num_phys_attrs * sizeof(bool));
	if (cstate->force_null)
	{
		List	   *attnums;
		ListCell   *cur;

		attnums = CopyGetAttnums(tupDesc, cstate->rel, cstate->force_null);

		foreach(cur, attnums)
		{
			int			attnum = lfirst_int(cur);
			Form_pg_attribute attr = TupleDescAttr(tupDesc, attnum - 1);

			if (!list_member_int(cstate->attnumlist, attnum))
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
						 errmsg("FORCE_NULL column \"%s\" not referenced by COPY",
								NameStr(attr->attname))));
			cstate->force_null_flags[attnum - 1] = true;
		}
	}

	/* Convert convert_selectively name list to per-column flags */
	if (cstate->convert_selectively)
	{
		List	   *attnums;
		ListCell   *cur;

		cstate->convert_select_flags = (bool *) palloc0(num_phys_attrs * sizeof(bool));

		attnums = CopyGetAttnums(tupDesc, cstate->rel, cstate->convert_select);

		foreach(cur, attnums)
		{
			int			attnum = lfirst_int(cur);
			Form_pg_attribute attr = TupleDescAttr(tupDesc, attnum - 1);

			if (!list_member_int(cstate->attnumlist, attnum))
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
						 errmsg_internal("selected column \"%s\" not referenced by COPY",
										 NameStr(attr->attname))));
			cstate->convert_select_flags[attnum - 1] = true;
		}
	}

	/* Use client encoding when ENCODING option is not specified. */
	if (cstate->file_encoding < 0)
		cstate->file_encoding = pg_get_client_encoding();

	/*
	 * Set up encoding conversion info.  Even if the file and server encodings
	 * are the same, we must apply pg_any_to_server() to validate data in
	 * multibyte encodings.
	 */
	cstate->need_transcoding =
		(cstate->file_encoding != GetDatabaseEncoding() ||
		 pg_database_encoding_max_length() > 1);
	/* See Multibyte encoding comment above */
	cstate->encoding_embeds_ascii = PG_ENCODING_IS_CLIENT_ONLY(cstate->file_encoding);

	cstate->copy_dest = COPY_FILE;	/* default */
	pgstat_progress_update_param(PROGRESS_COPY_STATUS, CP_IN_PROG);

	MemoryContextSwitchTo(oldcontext);

	return cstate;
}

/*
 * Closes the pipe to an external program, checking the pclose() return code.
 */
static void
ClosePipeToProgram(CopyState cstate)
{
	int			pclose_rc;

	Assert(cstate->is_program);

	pclose_rc = ClosePipeStream(cstate->copy_file);
	if (pclose_rc == -1)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close pipe to external command: %m")));
	else if (pclose_rc != 0)
	{
		/*
		 * If we ended a COPY FROM PROGRAM before reaching EOF, then it's
		 * expectable for the called program to fail with SIGPIPE, and we
		 * should not report that as an error.  Otherwise, SIGPIPE indicates a
		 * problem.
		 */
		if (cstate->is_copy_from && !cstate->reached_eof &&
			wait_result_is_signal(pclose_rc, SIGPIPE))
			return;

		ereport(ERROR,
				(errcode(ERRCODE_EXTERNAL_ROUTINE_EXCEPTION),
				 errmsg("program \"%s\" failed",
						cstate->filename),
				 errdetail_internal("%s", wait_result_to_str(pclose_rc))));
	}
}

/*
 * Release resources allocated in a cstate for COPY TO/FROM.
 */
static void
EndCopy(CopyState cstate)
{
	if (cstate->is_program)
	{
		ClosePipeToProgram(cstate);
	}
	else
	{
		if (cstate->filename != NULL && FreeFile(cstate->copy_file))
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not close file \"%s\": %m",
							cstate->filename)));
	}

	pgstat_progress_end_command();
	pgstat_progress_update_param(PROGRESS_COPY_STATUS, CP_SUCCESS);

	MemoryContextDelete(cstate->copycontext);
	pfree(cstate);
}

/*
 * Setup CopyState to read tuples from a table or a query for COPY TO.
 */
static CopyState
BeginCopyTo(ParseState *pstate,
			Relation rel,
			RawStmt *query,
			Oid queryRelId,
			const char *filename,
			bool is_program,
			List *attnamelist,
			List *options)
{
	CopyState	cstate;
	bool		pipe = (filename == NULL);
	MemoryContext oldcontext;
	const int	progress_cols[] = {
		PROGRESS_COPY_COMMAND,
		PROGRESS_COPY_TYPE
	};
	int64		progress_vals[] = {
		PROGRESS_COPY_COMMAND_TO,
		0
	};

	if (rel != NULL && rel->rd_rel->relkind != RELKIND_RELATION)
	{
		if (rel->rd_rel->relkind == RELKIND_VIEW)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy from view \"%s\"",
							RelationGetRelationName(rel)),
					 errhint("Try the COPY (SELECT ...) TO variant.")));
		else if (rel->rd_rel->relkind == RELKIND_MATVIEW)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy from materialized view \"%s\"",
							RelationGetRelationName(rel)),
					 errhint("Try the COPY (SELECT ...) TO variant.")));
		else if (rel->rd_rel->relkind == RELKIND_FOREIGN_TABLE)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy from foreign table \"%s\"",
							RelationGetRelationName(rel)),
					 errhint("Try the COPY (SELECT ...) TO variant.")));
		else if (rel->rd_rel->relkind == RELKIND_SEQUENCE)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy from sequence \"%s\"",
							RelationGetRelationName(rel))));
		else if (rel->rd_rel->relkind == RELKIND_PARTITIONED_TABLE)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy from partitioned table \"%s\"",
							RelationGetRelationName(rel)),
					 errhint("Try the COPY (SELECT ...) TO variant.")));
		else
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy from non-table relation \"%s\"",
							RelationGetRelationName(rel))));
	}

	cstate = BeginCopy(pstate, false, rel, query, queryRelId, attnamelist,
					   options);
	oldcontext = MemoryContextSwitchTo(cstate->copycontext);

	if (pipe)
	{
		progress_vals[1] = PROGRESS_COPY_TYPE_PIPE;

		Assert(!is_program);	/* the grammar does not allow this */
		if (whereToSendOutput != DestRemote)
			cstate->copy_file = stdout;
	}
	else
	{
		cstate->filename = pstrdup(filename);
		cstate->is_program = is_program;

		if (is_program)
		{
			progress_vals[1] = PROGRESS_COPY_TYPE_PROGRAM;
			cstate->copy_file = OpenPipeStream(cstate->filename, PG_BINARY_W);
			if (cstate->copy_file == NULL)
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not execute command \"%s\": %m",
								cstate->filename)));
		}
		else
		{
			mode_t		oumask; /* Pre-existing umask value */
			struct stat st;

			progress_vals[1] = PROGRESS_COPY_TYPE_FILE;
			/*
			 * Prevent write to relative path ... too easy to shoot oneself in
			 * the foot by overwriting a database file ...
			 */
			if (!is_absolute_path(filename))
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_NAME),
						 errmsg("relative path not allowed for COPY to file")));

			oumask = umask(S_IWGRP | S_IWOTH);
			PG_TRY();
			{
				cstate->copy_file = AllocateFile(cstate->filename, PG_BINARY_W);
			}
			PG_CATCH();
			{
				umask(oumask);
				PG_RE_THROW();
			}
			PG_END_TRY();
			umask(oumask);
			if (cstate->copy_file == NULL)
			{
				/* copy errno because ereport subfunctions might change it */
				int			save_errno = errno;

				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not open file \"%s\" for writing: %m",
								cstate->filename),
						 (save_errno == ENOENT || save_errno == EACCES) ?
						 errhint("COPY TO instructs the PostgreSQL server process to write a file. "
								 "You may want a client-side facility such as psql's \\copy.") : 0));
			}

			if (fstat(fileno(cstate->copy_file), &st))
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not stat file \"%s\": %m",
								cstate->filename)));

			if (S_ISDIR(st.st_mode))
				ereport(ERROR,
						(errcode(ERRCODE_WRONG_OBJECT_TYPE),
						 errmsg("\"%s\" is a directory", cstate->filename)));
		}
	}

	/* initialize progress */
	pgstat_progress_start_command(PROGRESS_COMMAND_COPY,
								  cstate->rel ? RelationGetRelid(cstate->rel) : InvalidOid);
	pgstat_progress_update_multi_param(2, progress_cols, progress_vals);

	cstate->bytes_processed = 0;

	MemoryContextSwitchTo(oldcontext);

	return cstate;
}

/*
 * This intermediate routine exists mainly to localize the effects of setjmp
 * so we don't need to plaster a lot of variables with "volatile".
 */
static uint64
DoCopyTo(CopyState cstate)
{
	bool		pipe = (cstate->filename == NULL);
	bool		fe_copy = (pipe && whereToSendOutput == DestRemote);
	uint64		processed;

	PG_TRY();
	{
		if (fe_copy)
			SendCopyBegin(cstate);

		processed = CopyTo(cstate);

		if (fe_copy)
			SendCopyEnd(cstate);
	}
	PG_CATCH();
	{
		/*
		 * Make sure we turn off old-style COPY OUT mode upon error. It is
		 * okay to do this in all cases, since it does nothing if the mode is
		 * not on.
		 */
		pq_endcopyout(true);
		PG_RE_THROW();
	}
	PG_END_TRY();

	return processed;
}

/*
 * Clean up storage and release resources for COPY TO.
 */
static void
EndCopyTo(CopyState cstate)
{
	if (cstate->queryDesc != NULL)
	{
		/* Close down the query and free resources. */
		ExecutorFinish(cstate->queryDesc);
		ExecutorEnd(cstate->queryDesc);
		FreeQueryDesc(cstate->queryDesc);
		PopActiveSnapshot();
	}

	/* Clean up storage */
	EndCopy(cstate);
}

/*
 * Copy from relation or query TO file.
 */
static uint64
CopyTo(CopyState cstate)
{
	TupleDesc	tupDesc;
	int			num_phys_attrs;
	ListCell   *cur;
	uint64		processed;

	if (cstate->rel)
		tupDesc = RelationGetDescr(cstate->rel);
	else
		tupDesc = cstate->queryDesc->tupDesc;
	num_phys_attrs = tupDesc->natts;
	cstate->null_print_client = cstate->null_print; /* default */

	/* We use fe_msgbuf as a per-row buffer regardless of copy_dest */
	cstate->fe_msgbuf = makeStringInfo();

	/* Get info about the columns we need to process. */
	cstate->out_functions = (FmgrInfo *) palloc(num_phys_attrs * sizeof(FmgrInfo));
	foreach(cur, cstate->attnumlist)
	{
		int			attnum = lfirst_int(cur);
		Oid			out_func_oid;
		bool		isvarlena;
		Form_pg_attribute attr = TupleDescAttr(tupDesc, attnum - 1);

		if (cstate->binary)
			getTypeBinaryOutputInfo(attr->atttypid,
									&out_func_oid,
									&isvarlena);
		else
			getTypeOutputInfo(attr->atttypid,
							  &out_func_oid,
							  &isvarlena);
		fmgr_info(out_func_oid, &cstate->out_functions[attnum - 1]);
	}

	/*
	 * Create a temporary memory context that we can reset once per row to
	 * recover palloc'd memory.  This avoids any problems with leaks inside
	 * datatype output routines, and should be faster than retail pfree's
	 * anyway.  (We don't need a whole econtext as CopyFrom does.)
	 */
	cstate->rowcontext = AllocSetContextCreate(GetCurrentMemoryContext(),
											   "COPY TO",
											   ALLOCSET_DEFAULT_SIZES);

	if (cstate->binary)
	{
		/* Generate header for a binary copy */
		int32		tmp;

		/* Signature */
		CopySendData(cstate, BinarySignature, 11);
		/* Flags field */
		tmp = 0;
		if (cstate->oids)
			tmp |= (1 << 16);
		CopySendInt32(cstate, tmp);
		/* No header extension */
		tmp = 0;
		CopySendInt32(cstate, tmp);
	}
	else
	{
		/*
		 * For non-binary copy, we need to convert null_print to file
		 * encoding, because it will be sent directly with CopySendString.
		 */
		if (cstate->need_transcoding)
			cstate->null_print_client = pg_server_to_any(cstate->null_print,
														 cstate->null_print_len,
														 cstate->file_encoding);

		/* if a header has been requested send the line */
		if (cstate->header_line)
		{
			bool		hdr_delim = false;

			foreach(cur, cstate->attnumlist)
			{
				int			attnum = lfirst_int(cur);
				char	   *colname;

				if (hdr_delim)
					CopySendChar(cstate, cstate->delim[0]);
				hdr_delim = true;

				colname = NameStr(TupleDescAttr(tupDesc, attnum - 1)->attname);

				CopyAttributeOutCSV(cstate, colname, false,
									list_length(cstate->attnumlist) == 1);
			}

			CopySendEndOfRow(cstate);
		}
	}

	if (cstate->rel)
	{
		Datum	   *values;
		bool	   *nulls;
		HeapScanDesc scandesc;
		HeapTuple	tuple;
		bool		is_yb_relation;
		MemoryContext oldcontext;
		MemoryContext yb_context;

		values = (Datum *) palloc(num_phys_attrs * sizeof(Datum));
		nulls = (bool *) palloc(num_phys_attrs * sizeof(bool));

		scandesc = heap_beginscan(cstate->rel, GetActiveSnapshot(), 0, NULL);
		is_yb_relation = IsYBRelation(cstate->rel);

		/*
		 * Create and switch to a temporary memory context that we can reset
		 * once per row to recover Yugabyte palloc'd memory.
		 */
		if (is_yb_relation)
		{
			yb_context = AllocSetContextCreate(GetCurrentMemoryContext(),
											   "COPY TO (YB)",
											   ALLOCSET_DEFAULT_SIZES);
			oldcontext = MemoryContextSwitchTo(yb_context);
		}

		processed = 0;
		while ((tuple = heap_getnext(scandesc, ForwardScanDirection)) != NULL)
		{
			CHECK_FOR_INTERRUPTS();

			/* Deconstruct the tuple ... faster than repeated heap_getattr */
			heap_deform_tuple(tuple, tupDesc, values, nulls);

			/* Format and send the data */
			CopyOneRowTo(cstate, HeapTupleGetOid(tuple), values, nulls);

			/*
			 * Increment the number of processed tuples, and report the
			 * progress.
			 */
			pgstat_progress_update_param(PROGRESS_COPY_TUPLES_PROCESSED,
										 ++processed);

			/* Free Yugabyte memory for this row */
			if (is_yb_relation)
				MemoryContextReset(yb_context);
		}

		/*
		 * Switch out of and delete the temporary memory context for Yugabyte
		 * palloc'd memory.
		 */
		if (is_yb_relation)
		{
			MemoryContextSwitchTo(oldcontext);
			MemoryContextDelete(yb_context);
		}

		heap_endscan(scandesc);

		pfree(values);
		pfree(nulls);
	}
	else
	{
		/* run the plan --- the dest receiver will send tuples */
		ExecutorRun(cstate->queryDesc, ForwardScanDirection, 0L, true);
		processed = ((DR_copy *) cstate->queryDesc->dest)->processed;
	}

	if (cstate->binary)
	{
		/* Generate trailer for a binary copy */
		CopySendInt16(cstate, -1);
		/* Need to flush out the trailer */
		CopySendEndOfRow(cstate);
	}

	MemoryContextDelete(cstate->rowcontext);

	return processed;
}

/*
 * Emit one row during CopyTo().
 */
static void
CopyOneRowTo(CopyState cstate, Oid tupleOid, Datum *values, bool *nulls)
{
	bool		need_delim = false;
	FmgrInfo   *out_functions = cstate->out_functions;
	MemoryContext oldcontext;
	ListCell   *cur;
	char	   *string;

	MemoryContextReset(cstate->rowcontext);
	oldcontext = MemoryContextSwitchTo(cstate->rowcontext);

	if (cstate->binary)
	{
		/* Binary per-tuple header */
		CopySendInt16(cstate, list_length(cstate->attnumlist));
		/* Send OID if wanted --- note attnumlist doesn't include it */
		if (cstate->oids)
		{
			/* Hack --- assume Oid is same size as int32 */
			CopySendInt32(cstate, sizeof(int32));
			CopySendInt32(cstate, tupleOid);
		}
	}
	else
	{
		/* Text format has no per-tuple header, but send OID if wanted */
		/* Assume digits don't need any quoting or encoding conversion */
		if (cstate->oids)
		{
			string = DatumGetCString(DirectFunctionCall1(oidout,
														 ObjectIdGetDatum(tupleOid)));
			CopySendString(cstate, string);
			need_delim = true;
		}
	}

	foreach(cur, cstate->attnumlist)
	{
		int			attnum = lfirst_int(cur);
		Datum		value = values[attnum - 1];
		bool		isnull = nulls[attnum - 1];

		if (!cstate->binary)
		{
			if (need_delim)
				CopySendChar(cstate, cstate->delim[0]);
			need_delim = true;
		}

		if (isnull)
		{
			if (!cstate->binary)
				CopySendString(cstate, cstate->null_print_client);
			else
				CopySendInt32(cstate, -1);
		}
		else
		{
			if (!cstate->binary)
			{
				string = OutputFunctionCall(&out_functions[attnum - 1],
											value);
				if (cstate->csv_mode)
					CopyAttributeOutCSV(cstate, string,
										cstate->force_quote_flags[attnum - 1],
										list_length(cstate->attnumlist) == 1);
				else
					CopyAttributeOutText(cstate, string);
			}
			else
			{
				bytea	   *outputbytes;

				outputbytes = SendFunctionCall(&out_functions[attnum - 1],
											   value);
				CopySendInt32(cstate, VARSIZE(outputbytes) - VARHDRSZ);
				CopySendData(cstate, VARDATA(outputbytes),
							 VARSIZE(outputbytes) - VARHDRSZ);
			}
		}
	}

	CopySendEndOfRow(cstate);

	MemoryContextSwitchTo(oldcontext);
}


/*
 * error context callback for COPY FROM
 *
 * The argument for the error context must be CopyState.
 */
void
CopyFromErrorCallback(void *arg)
{
	CopyState	cstate = (CopyState) arg;
	char		curlineno_str[32];

	snprintf(curlineno_str, sizeof(curlineno_str), UINT64_FORMAT,
			 cstate->cur_lineno);
	pgstat_progress_update_param(PROGRESS_COPY_STATUS, CP_ERROR);

	if (cstate->binary)
	{
		/* can't usefully display the data */
		if (cstate->cur_attname)
			errcontext("COPY %s, line %s, column %s",
					   cstate->cur_relname, curlineno_str,
					   cstate->cur_attname);
		else
			errcontext("COPY %s, line %s",
					   cstate->cur_relname, curlineno_str);
	}
	else
	{
		if (cstate->cur_attname && cstate->cur_attval)
		{
			/* error is relevant to a particular column */
			char	   *attval;

			attval = limit_printout_length(cstate->cur_attval);
			errcontext("COPY %s, line %s, column %s: \"%s\"",
					   cstate->cur_relname, curlineno_str,
					   cstate->cur_attname, attval);
			pfree(attval);
		}
		else if (cstate->cur_attname)
		{
			/* error is relevant to a particular column, value is NULL */
			errcontext("COPY %s, line %s, column %s: null input",
					   cstate->cur_relname, curlineno_str,
					   cstate->cur_attname);
		}
		else
		{
			/*
			 * Error is relevant to a particular line.
			 *
			 * If line_buf still contains the correct line, and it's already
			 * transcoded, print it. If it's still in a foreign encoding, it's
			 * quite likely that the error is precisely a failure to do
			 * encoding conversion (ie, bad data). We dare not try to convert
			 * it, and at present there's no way to regurgitate it without
			 * conversion. So we have to punt and just report the line number.
			 */
			if (cstate->line_buf_valid &&
				(cstate->line_buf_converted || !cstate->need_transcoding))
			{
				char	   *lineval;

				lineval = limit_printout_length(cstate->line_buf.data);
				errcontext("COPY %s, line %s: \"%s\"",
						   cstate->cur_relname, curlineno_str, lineval);
				pfree(lineval);
			}
			else
			{
				errcontext("COPY %s, line %s",
						   cstate->cur_relname, curlineno_str);
			}
		}
	}
}

/*
 * Make sure we don't print an unreasonable amount of COPY data in a message.
 *
 * It would seem a lot easier to just use the sprintf "precision" limit to
 * truncate the string.  However, some versions of glibc have a bug/misfeature
 * that vsnprintf will always fail (return -1) if it is asked to truncate
 * a string that contains invalid byte sequences for the current encoding.
 * So, do our own truncation.  We return a pstrdup'd copy of the input.
 */
static char *
limit_printout_length(const char *str)
{
#define MAX_COPY_DATA_DISPLAY 100

	int			slen = strlen(str);
	int			len;
	char	   *res;

	/* Fast path if definitely okay */
	if (slen <= MAX_COPY_DATA_DISPLAY)
		return pstrdup(str);

	/* Apply encoding-dependent truncation */
	len = pg_mbcliplen(str, slen, MAX_COPY_DATA_DISPLAY);

	/*
	 * Truncate, and add "..." to show we truncated the input.
	 */
	res = (char *) palloc(len + 4);
	memcpy(res, str, len);
	strcpy(res + len, "...");

	return res;
}

/*
 * Copy FROM file to relation.
 */
uint64
CopyFrom(CopyState cstate)
{
	HeapTuple	tuple;
	TupleDesc	tupDesc;
	Datum	   *values;
	bool	   *nulls;
	ResultRelInfo *resultRelInfo;
	ResultRelInfo *saved_resultRelInfo = NULL;
	EState	   *estate = CreateExecutorState(); /* for ExecConstraints() */
	ModifyTableState *mtstate;
	ExprContext *econtext;
	TupleTableSlot *myslot;
	MemoryContext oldcontext = GetCurrentMemoryContext();

	ErrorContextCallback errcallback;
	CommandId	mycid = GetCurrentCommandId(true);
	int			hi_options = 0; /* start with default heap_insert options */
	BulkInsertState bistate;
	int64		processed = 0;
	bool		useMultiInsert;
	bool		useYBMultiInsert;
	bool		useHeapMultiInsert;
	int			nBufferedTuples = 0;
	int			prev_leaf_part_index = -1;
	bool		useNonTxnInsert;

	/*
	 * If the batch size is not explicitly set in the query by the user,
	 * use the session variable value.
	 */
	if (cstate->batch_size < 0)
	{
		cstate->batch_size = yb_default_copy_from_rows_per_transaction;
	}

#define MAX_BUFFERED_TUPLES 1000
	HeapTuple  *bufferedTuples = NULL;	/* initialize to silence warning */
	Size		bufferedTuplesSize = 0;
	uint64		firstBufferedLineNo = 0;

	Assert(cstate->rel);

	/*
	 * The target must be a plain, foreign, or partitioned relation, or have
	 * an INSTEAD OF INSERT row trigger.  (Currently, such triggers are only
	 * allowed on views, so we only hint about them in the view case.)
	 */
	if (cstate->rel->rd_rel->relkind != RELKIND_RELATION &&
		cstate->rel->rd_rel->relkind != RELKIND_FOREIGN_TABLE &&
		cstate->rel->rd_rel->relkind != RELKIND_PARTITIONED_TABLE &&
		!(cstate->rel->trigdesc &&
		  cstate->rel->trigdesc->trig_insert_instead_row))
	{
		if (cstate->rel->rd_rel->relkind == RELKIND_VIEW)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy to view \"%s\"",
							RelationGetRelationName(cstate->rel)),
					 errhint("To enable copying to a view, provide an INSTEAD OF INSERT trigger.")));
		else if (cstate->rel->rd_rel->relkind == RELKIND_MATVIEW)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy to materialized view \"%s\"",
							RelationGetRelationName(cstate->rel))));
		else if (cstate->rel->rd_rel->relkind == RELKIND_SEQUENCE)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy to sequence \"%s\"",
							RelationGetRelationName(cstate->rel))));
		else
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot copy to non-table relation \"%s\"",
							RelationGetRelationName(cstate->rel))));
	}

	tupDesc = RelationGetDescr(cstate->rel);

	/*----------
	 * Check to see if we can avoid writing WAL
	 *
	 * If archive logging/streaming is not enabled *and* either
	 *	- table was created in same transaction as this COPY
	 *	- data is being written to relfilenode created in this transaction
	 * then we can skip writing WAL.  It's safe because if the transaction
	 * doesn't commit, we'll discard the table (or the new relfilenode file).
	 * If it does commit, we'll have done the heap_sync at the bottom of this
	 * routine first.
	 *
	 * As mentioned in comments in utils/rel.h, the in-same-transaction test
	 * is not always set correctly, since in rare cases rd_newRelfilenodeSubid
	 * can be cleared before the end of the transaction. The exact case is
	 * when a relation sets a new relfilenode twice in same transaction, yet
	 * the second one fails in an aborted subtransaction, e.g.
	 *
	 * BEGIN;
	 * TRUNCATE t;
	 * SAVEPOINT save;
	 * TRUNCATE t;
	 * ROLLBACK TO save;
	 * COPY ...
	 *
	 * Also, if the target file is new-in-transaction, we assume that checking
	 * FSM for free space is a waste of time, even if we must use WAL because
	 * of archiving.  This could possibly be wrong, but it's unlikely.
	 *
	 * The comments for heap_insert and RelationGetBufferForTuple specify that
	 * skipping WAL logging is only safe if we ensure that our tuples do not
	 * go into pages containing tuples from any other transactions --- but this
	 * must be the case if we have a new table or new relfilenode, so we need
	 * no additional work to enforce that.
	 *
	 * We currently don't support this optimization if the COPY target is a
	 * partitioned table as we currently only lazily initialize partition
	 * information when routing the first tuple to the partition.  We cannot
	 * know at this stage if we can perform this optimization.  It should be
	 * possible to improve on this, but it does mean maintaining heap insert
	 * option flags per partition and setting them when we first open the
	 * partition.
	 *
	 * This optimization is not supported for relation types which do not
	 * have any physical storage, with foreign tables and views using
	 * INSTEAD OF triggers entering in this category.  Partitioned tables
	 * are not supported as per the description above.
	 *----------
	 */
	/* createSubid is creation check, newRelfilenodeSubid is truncation check */
	if (cstate->rel->rd_rel->relkind != RELKIND_FOREIGN_TABLE &&
		cstate->rel->rd_rel->relkind != RELKIND_PARTITIONED_TABLE &&
		cstate->rel->rd_rel->relkind != RELKIND_VIEW &&
		(cstate->rel->rd_createSubid != InvalidSubTransactionId ||
		 cstate->rel->rd_newRelfilenodeSubid != InvalidSubTransactionId))
	{
		hi_options |= HEAP_INSERT_SKIP_FSM;
		if (!XLogIsNeeded())
			hi_options |= HEAP_INSERT_SKIP_WAL;
	}

	/*
	 * Optimize if new relfilenode was created in this subxact or one of its
	 * committed children and we won't see those rows later as part of an
	 * earlier scan or command. The subxact test ensures that if this subxact
	 * aborts then the frozen rows won't be visible after xact cleanup.  Note
	 * that the stronger test of exactly which subtransaction created it is
	 * crucial for correctness of this optimization. The test for an earlier
	 * scan or command tolerates false negatives. FREEZE causes other sessions
	 * to see rows they would not see under MVCC, and a false negative merely
	 * spreads that anomaly to the current session.
	 */
	if (cstate->freeze)
	{
		/*
		 * We currently disallow COPY FREEZE on partitioned tables.  The
		 * reason for this is that we've simply not yet opened the partitions
		 * to determine if the optimization can be applied to them.  We could
		 * go and open them all here, but doing so may be quite a costly
		 * overhead for small copies.  In any case, we may just end up routing
		 * tuples to a small number of partitions.  It seems better just to
		 * raise an ERROR for partitioned tables.
		 */
		if (cstate->rel->rd_rel->relkind == RELKIND_PARTITIONED_TABLE)
		{
			ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("cannot perform FREEZE on a partitioned table")));
		}

		/*
		 * Tolerate one registration for the benefit of FirstXactSnapshot.
		 * Scan-bearing queries generally create at least two registrations,
		 * though relying on that is fragile, as is ignoring ActiveSnapshot.
		 * Clear CatalogSnapshot to avoid counting its registration.  We'll
		 * still detect ongoing catalog scans, each of which separately
		 * registers the snapshot it uses.
		 */
		InvalidateCatalogSnapshot();
		if (!ThereAreNoPriorRegisteredSnapshots() || !ThereAreNoReadyPortals())
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
					 errmsg("cannot perform FREEZE because of prior transaction activity")));

		if (cstate->rel->rd_createSubid != GetCurrentSubTransactionId() &&
			cstate->rel->rd_newRelfilenodeSubid != GetCurrentSubTransactionId())
			ereport(ERROR,
					(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
					 errmsg("cannot perform FREEZE because the table was not created or truncated in the current subtransaction")));

		hi_options |= HEAP_INSERT_FROZEN;
	}

	/*
	 * We need a ResultRelInfo so we can use the regular executor's
	 * index-entry-making machinery.  (There used to be a huge amount of code
	 * here that basically duplicated execUtils.c ...)
	 */
	resultRelInfo = makeNode(ResultRelInfo);
	InitResultRelInfo(resultRelInfo,
					  cstate->rel,
					  1,		/* dummy rangetable index */
					  NULL,
					  0);

	/* Verify the named relation is a valid target for INSERT */
	CheckValidResultRel(resultRelInfo, CMD_INSERT);

	ExecOpenIndices(resultRelInfo, false);

	estate->es_result_relations = resultRelInfo;
	estate->es_num_result_relations = 1;
	estate->es_result_relation_info = resultRelInfo;
	estate->es_range_table = cstate->range_table;
	estate->yb_es_is_fk_check_disabled = cstate->disable_fk_check;

	/* Set up a tuple slot too */
	myslot = ExecInitExtraTupleSlot(estate, tupDesc);
	/* Triggers might need a slot as well */
	estate->es_trig_tuple_slot = ExecInitExtraTupleSlot(estate, NULL);

	/*
	 * Set up a ModifyTableState so we can let FDW(s) init themselves for
	 * foreign-table result relation(s).
	 */
	mtstate = makeNode(ModifyTableState);
	mtstate->ps.plan = NULL;
	mtstate->ps.state = estate;
	mtstate->operation = CMD_INSERT;
	mtstate->resultRelInfo = estate->es_result_relations;
	mtstate->rootResultRelInfo = estate->es_result_relations;

	if (resultRelInfo->ri_FdwRoutine != NULL &&
		resultRelInfo->ri_FdwRoutine->BeginForeignInsert != NULL)
		resultRelInfo->ri_FdwRoutine->BeginForeignInsert(mtstate,
														 resultRelInfo);

	/* Prepare to catch AFTER triggers. */
	AfterTriggerBeginQuery();

	/*
	 * If there are any triggers with transition tables on the named relation,
	 * we need to be prepared to capture transition tuples.
	 */
	cstate->transition_capture =
		MakeTransitionCaptureState(cstate->rel->trigdesc,
								   RelationGetRelid(cstate->rel),
								   CMD_INSERT);

	/*
	 * If the named relation is a partitioned table, initialize state for
	 * CopyFrom tuple routing.
	 */
	if (cstate->rel->rd_rel->relkind == RELKIND_PARTITIONED_TABLE)
	{
		PartitionTupleRouting *proute;

		proute = cstate->partition_tuple_routing =
			ExecSetupPartitionTupleRouting(NULL, resultRelInfo);

		/*
		 * If we are capturing transition tuples, they may need to be
		 * converted from partition format back to partitioned table format
		 * (this is only ever necessary if a BEFORE trigger modifies the
		 * tuple).
		 */
		if (cstate->transition_capture != NULL)
			ExecSetupChildParentMapForLeaf(proute);
	}

	if (cstate->batch_size > 0)
	{
		/*
		 * Batched copy is not supported
		 * under the following use cases in which case
		 * all rows will be copied over in a single transaction.
		 */
		int batch_size = 0;

		if (!IsYBRelation(resultRelInfo->ri_RelationDesc))
		{
			Assert(resultRelInfo->ri_RelationDesc->rd_rel->relpersistence == RELPERSISTENCE_TEMP ||
					resultRelInfo->ri_RelationDesc->rd_rel->relkind == RELKIND_FOREIGN_TABLE);
			ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
			 	 errmsg("Batched COPY is not supported on %s tables. "
						"Defaulting to using one transaction for the entire copy.",
						YbIsTempRelation(resultRelInfo->ri_RelationDesc) ? "temporary" : "foreign"),
				 errhint("Either copy onto non-temporary table or set rows_per_transaction "
						 "option to `0` to disable batching and remove this warning.")));
		}
		else if (YBIsDataSent())
			ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("Batched COPY is not supported in transaction blocks. "
						"Defaulting to using one transaction for the entire copy."),
				 errhint("Either run this COPY outside of a transaction block or set "
						 "rows_per_transaction option to `0` to disable batching and "
						 "remove this warning.")));
		else if (HasNonRITrigger(cstate->rel->trigdesc))
			ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
			 	 errmsg("Batched COPY is not supported on table with non RI trigger. "
						"Defaulting to using one transaction for the entire copy."),
				 errhint("Set rows_per_transaction option to `0` to disable batching "
				 		 "and remove this warning.")));
		else			
			batch_size = cstate->batch_size;

		cstate->batch_size = batch_size;
=======
	else
	{
		/* Validate the user-supplied list and extract attnums */
		ListCell   *l;

		foreach(l, attnamelist)
		{
			char	   *name = strVal(lfirst(l));
			int			attnum;
			int			i;

			/* Lookup column name */
			attnum = InvalidAttrNumber;
			for (i = 0; i < tupDesc->natts; i++)
			{
				Form_pg_attribute att = TupleDescAttr(tupDesc, i);

				if (att->attisdropped)
					continue;
				if (namestrcmp(&(att->attname), name) == 0)
				{
					if (att->attgenerated)
						ereport(ERROR,
								(errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
								 errmsg("column \"%s\" is a generated column",
										name),
								 errdetail("Generated columns cannot be used in COPY.")));
					attnum = att->attnum;
					break;
				}
			}
			if (attnum == InvalidAttrNumber)
			{
				if (rel != NULL)
					ereport(ERROR,
							(errcode(ERRCODE_UNDEFINED_COLUMN),
							 errmsg("column \"%s\" of relation \"%s\" does not exist",
									name, RelationGetRelationName(rel))));
				else
					ereport(ERROR,
							(errcode(ERRCODE_UNDEFINED_COLUMN),
							 errmsg("column \"%s\" does not exist",
									name)));
			}
			/* Check for duplicates */
			if (list_member_int(attnums, attnum))
				ereport(ERROR,
						(errcode(ERRCODE_DUPLICATE_COLUMN),
						 errmsg("column \"%s\" specified more than once",
								name)));
			attnums = lappend_int(attnums, attnum);
		}
>>>>>>> copy.c
	}

	return attnums;
}
