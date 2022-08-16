---
title: Transaction priorities
headerTitle: Transaction priorities
linkTitle: Transaction priorities
description: Transaction priorities in YugabyteDB.
headcontent: Transaction priorities in YugabyteDB.
image: <div class="icon"><i class="fas fa-file-invoice-dollar"></i></div>
menu:
  stable:
    name: Transaction priorities
    identifier: develop-quality-of-service-transaction-priorities
    parent: develop-quality-of-service
    weight: 235
type: docs
---

YugabyteDB allows external applications to set the priority of individual transactions. When using optimistic concurrency control, it is possible to ensure that a *higher priority* transaction gets priority over a lower priority transaction. In this scenario, if these transactions conflict, the *lower priority* transaction is aborted. This behavior can be achieved by setting the pair of session variables `yb_transaction_priority_lower_bound`, and `yb_transaction_priority_upper_bound`. A random number between the lower and upper bound is computed and assigned as the transaction priority for the transactions in that session. If this transaction conflicts with another, the value of transaction priority is compared with that of the conflicting transaction. The transaction with a higher priority value wins. To view the transaction priority of the active transaction in current session, run `SHOW yb_transaction_priority` inside the transaction block. If `SHOW yb_transaction_priority` is run outside a transaction block, it will output 0.

| Flag | Valid Range | Description |
| --- | --- | --- |
| `yb_transaction_priority_lower_bound` | Any value between 0 and 1, lower than the upper bound | Minimum transaction priority for transactions run in this session |
| `yb_transaction_priority_upper_bound` | Any value between 0 and 1, higher than the lower bound | Maximum transaction priority for transactions run in this session |
| `yb_transaction_priority` (read-only) | Displays the priority type: Normal, High or Highest. For Normal and High priority transaction, a numerical value is also shown for the transaction's priority. |

{{< note title="Note" >}}
Currently, transaction priorities work in the following scenarios:

* Works with YSQL only, not supported for YCQL.
* Can be used only with optimistic concurrency control, not yet implemented for pessimistic concurrency control.
* Only conflict resolution is prioritized, not resource consumption as a part.

Some of the improvements are planned.

{{< /note >}}

It is possible to set the priority of a transaction using the two session variables `yb_transaction_priority_lower_bound` and `yb_transaction_priority_upper_bound`, each of which can be set to a value between 0.0 and 1.0, as shown in the following example. When a transaction is executed, a random priority between the lower and upper bound is assigned to it.

## Examples

Let's create a [YugabyteDB cluster](../../../quick-start/), and open two separate [ysqlsh](../../../admin/ysqlsh/#starting-ysqlsh) connections to it.

{{< tip title="Tip - Use YugabyteDB Managed" >}}
You can create a cluster in the free tier of [YugabyteDB Managed](/preview/quick-start-yugabytedb-managed/), and open two *cloud shell* connections to it. These cloud shell connections open up in two different browser tabs, which can be used to do the steps below.

{{< /tip >}}

### Transaction priority between concurrent operations

Let's create an example scenario of an accounts table, and insert a row into as follows:

```sql
create table account
  (
    name text not null,
    type text not null,
    balance money not null default '0.00'::money,
    primary key (name, type)
  );
insert into account values
  ('kevin','saving', 500),
  ('kevin','checking', 500);
```

Now, we're going to perform a deposit and a withdrawal at the same time. Also, assume we want to give higher priority to deposit transactions (when compared to withdrawals). To simulate this, we're going to perform two operations concurrently - a withdrawal in one session, and a deposit from a separate session. The deposit transaction starts after the withdrawal is initiated, but occurs before the withdrawal is completed from a separate session. This is shown below.

<table style="margin:0 5px;">
  <tr>
   <td style="text-align:center;"><span style="font-size: 22px;">session #1 (withdrawal, low priority)</span></td>
   <td style="text-align:center; border-left:1px solid rgba(158,159,165,0.5);"><span style="font-size: 22px;">session #2 (deposit, high priority)</span></td>
  </tr>

  <tr>
    <td style="width:50%;">
    Set the transaction priority to a lower range.
    <pre><code style="padding: 0 10px;">
set yb_transaction_priority_lower_bound = 0.4;
set yb_transaction_priority_upper_bound= 0.6;
    </code></pre>
    </td>
    <td style="width:50%; border-left:1px solid rgba(158,159,165,0.5);">
    Set the transaction priority to a higher range.
    <pre><code style="padding: 0 10px;">
set yb_transaction_priority_lower_bound = 0.7;
set yb_transaction_priority_upper_bound= 0.9;
    </code></pre>
    </td>
  </tr>

  <tr>
    <td style="width:50%;">
    Initiate the withdrawal of $100.
    <pre><code style="padding: 0 10px;">
begin transaction /*lower priority transaction*/;
update account set balance = balance - 100::money
    where name='kevin' and type='checking';
    </code></pre>
    The transaction has started, though not committed yet.
    <pre><code style="padding: 0 10px;">
select * from account;
 name  |   type   | balance
-------+----------+---------
 kevin | checking | $400.00
 kevin | saving   | $500.00
(2 rows)
    </code></pre>
    </td>
    <td style="width:50%; border-left:1px solid rgba(158,159,165,0.5);">
    </td>
  </tr>

  <tr>
    <td style="width:50%; border-left:1px solid rgba(158,159,165,0.5);">
    </td>
    <td style="width:50%;">
    Next, initiate the deposit of $200, which should have higher priority.
    <pre><code style="padding: 0 10px;">
begin transaction /*high priority transaction*/;
update account set balance = balance + 200::money
    where name='kevin' and type='checking';
    </code></pre>
    The transaction has started, though not committed yet.
    <pre><code style="padding: 0 10px;">
select * from account;
 name  |   type   | balance
-------+----------+---------
 kevin | checking | $700.00
 kevin | saving   | $500.00
(2 rows)
    </code></pre>
    </td>
  </tr>

  <tr>
    <td style="width:50%;">
    The withdrawal transaction will now abort because it conflicts with the higher priority deposit transaction.
    <pre><code style="padding: 0 10px;">
select * from account;
ERROR:  Operation failed. Try again: Unknown transaction,
        could be recently aborted: XXXX
    </code></pre>
    </td>
    <td style="width:50%; border-left:1px solid rgba(158,159,165,0.5);">
    </td>
  </tr>

  <tr>
    <td style="width:50%; border-left:1px solid rgba(158,159,165,0.5);">
    </td>
    <td style="width:50%;">
    The deposit transaction can now commit.
    <pre><code style="padding: 0 10px;">
commit;
COMMIT
yugabyte=> select * from account;
 name  |   type   | balance
-------+----------+---------
 kevin | checking | $700.00
 kevin | saving   | $500.00
(2 rows)
    </code></pre>
    </td>
  </tr>

</table>

### Show transaction priority types

The following example demonstrates the usage of `yb_transaction_priority` based on the priority types.

1. From an active [ysqlsh](../../../admin/ysqlsh/#starting-ysqlsh) shell, create a table as follows:

    ```sql
    CREATE TABLE test_scan (i int, j int);
    ```

1. Start by setting the lower and upper bound values for your transaction.

    ```sql
    set yb_transaction_priority_lower_bound = 0.4;
    set yb_transaction_priority_upper_bound = 0.6;
    ```

1. In a transaction block, perform an insert and view the transaction priority as follows:

    ```sql
    BEGIN TRANSACTION;
    INSERT INTO test_scan (i, j) values (1, 1), (2, 2), (3, 3);
    show yb_transaction_priority;
    COMMIT;
    ```

    ```output
              yb_transaction_priority
    -------------------------------------------
      0.537144608 (Normal priority transaction)
    (1 row)
    ```

1. In the next transaction block, perform a `SELECT ... FOR UPDATE`, which results in a high priority transaction.

    ```sql
    set yb_transaction_priority_lower_bound = 0.1;
    set yb_transaction_priority_lower_bound = 0.4;
    BEGIN TRANSACTION;
    SELECT i, j FROM test_scan WHERE i = 1 FOR UPDATE;
    show yb_transaction_priority;
    COMMIT;
    ```

    ```output
        yb_transaction_priority
    -------------------------------------------
     0.212004009 (High priority transaction)
    (1 row)
    ```

   As seen from the resulting _High priority transaction_ value above, it is randomly chosen between the lower and upper bound.

1. In the final transaction block, set `yb_transaction_priority_upper_bound` and `yb_transaction_priority_lower_bound` to be 1, and perform the same `SELECT ... FOR UPDATE` query as the previous one. This transaction type is of the highest priority.

    ```sql
    set yb_transaction_priority_upper_bound = 1;
    set yb_transaction_priority_lower_bound = 1;
    BEGIN TRANSACTION;
    SELECT i, j FROM test_scan WHERE i = 1 FOR UPDATE;
    show yb_transaction_priority;
    COMMIT;
    ```

    ```output
        yb_transaction_priority
    -------------------------------------------
    Highest priority transaction
    (1 row)
    ```

1. View the transaction priority outside a transaction block as follows:

    ```sql
    show yb_transaction_priority;
    ```

    ```output
                 yb_transaction_priority
    -------------------------------------------
     0.000000000 (Normal priority transaction)
    (1 row)
    ```