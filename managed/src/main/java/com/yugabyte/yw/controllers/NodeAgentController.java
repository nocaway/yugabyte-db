// Copyright (c) Yugabyte, Inc.

package com.yugabyte.yw.controllers;

import com.yugabyte.yw.controllers.handlers.NodeAgentHandler;
import com.yugabyte.yw.forms.PlatformResults;
import com.yugabyte.yw.forms.PlatformResults.YBPSuccess;
import com.yugabyte.yw.models.Audit;
import com.yugabyte.yw.models.Customer;
import com.yugabyte.yw.models.NodeAgent;
import io.swagger.annotations.Api;
import java.util.UUID;
import javax.inject.Inject;
import play.mvc.Result;

@Api(hidden = true)
public class NodeAgentController extends AuthenticatedController {

  @Inject NodeAgentHandler nodeAgentHandler;

  public Result register(UUID customerUuid) {
    Customer.getOrBadRequest(customerUuid);
    NodeAgent nodeAgent = parseJsonAndValidate(NodeAgent.class);
    nodeAgent.customerUuid = customerUuid;
    nodeAgentHandler.register(nodeAgent);
    auditService()
        .createAuditEntryWithReqBody(
            ctx(),
            Audit.TargetType.NodeAgent,
            nodeAgent.uuid.toString(),
            Audit.ActionType.AddNodeAgent);
    return PlatformResults.withData(nodeAgent);
  }

  public Result get(UUID customerUuid, UUID nodeUuid) {
    NodeAgent nodeAgent = nodeAgentHandler.get(customerUuid, nodeUuid);
    return PlatformResults.withData(nodeAgent);
  }

  public Result unregister(UUID customerUuid, UUID nodeUuid) {
    NodeAgent.getOrBadRequest(customerUuid, nodeUuid);
    nodeAgentHandler.unregister(nodeUuid);
    auditService()
        .createAuditEntryWithReqBody(
            ctx(),
            Audit.TargetType.NodeAgent,
            nodeUuid.toString(),
            Audit.ActionType.DeleteNodeAgent);
    return YBPSuccess.empty();
  }
}