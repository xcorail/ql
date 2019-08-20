/**
 * Provides classes for importing source, sink and flow step summaries
 * through external predicates.
 */

import javascript
import semmle.javascript.dataflow.Portals
import external.ExternalArtifact
import Shared

/**
 * An external predicate providing information about additional sources.
 *
 * This predicate can be populated from the output of the `ExtractSourceSummaries` query.
 */
external predicate additionalSources(string portal, string flowLabel, string config);

/**
 * An external predicate providing information about additional sinks.
 *
 * This predicate can be populated from the output of the `ExtractSinkSummaries` query.
 */
external predicate additionalSinks(string portal, string flowLabel, string config);

/**
 * An external predicate providing information about additional flow steps.
 *
 * This predicate can be populated from the output of the `ExtractFlowStepSummaries` query.
 */
external predicate additionalSteps(
  string startPortal, string startFlowLabel, string endPortal, string endFlowLabel, string config
);

/**
 * An additional source specified through the `additionalSources` predicate.
 */
private class AdditionalSourceFromSpec extends DataFlow::AdditionalSource {
  Portal portal;

  string flowLabel;

  string config;

  AdditionalSourceFromSpec() {
    additionalSources(portal.toString(), flowLabel, config) and
    this = portal.getAnExitNode(_)
  }

  override predicate isSourceFor(DataFlow::Configuration cfg, DataFlow::FlowLabel lbl) {
    configSpec(cfg, config) and sourceFlowLabelSpec(lbl, flowLabel)
  }
}

/**
 * An additional sink specified through the `additionalSinks` predicate.
 */
private class AdditionalSinkFromSpec extends DataFlow::AdditionalSink {
  Portal portal;

  string flowLabel;

  string config;

  AdditionalSinkFromSpec() {
    additionalSinks(portal.toString(), flowLabel, config) and
    this = portal.getAnEntryNode(_)
  }

  override predicate isSinkFor(DataFlow::Configuration cfg, DataFlow::FlowLabel lbl) {
    configSpec(cfg, config) and sinkFlowLabelSpec(lbl, flowLabel)
  }
}

private class AdditionalFlowThroughSummaryFromSpec extends DataFlow::Configuration {
  DataFlow::Node entry;

  string startFlowLabel;

  DataFlow::Node exit;

  string endFlowLabel;

  AdditionalFlowThroughSummaryFromSpec() {
    exists(
      Portal base, int i, ParameterPortal parm, ReturnPortal ret, DataFlow::InvokeNode invk,
      string config
    |
      additionalSteps(parm.toString(), startFlowLabel, ret.toString(), endFlowLabel, config) and
      configSpec(this, config) and
      base = parm.getBasePortal() and
      i = parm.getIndex() and
      base = ret.getBasePortal() and
      invk = base.getAnExitNode(_).getAnInvocation()
    |
      entry = invk.getArgument(i) and
      exit = invk
    )
  }

  override predicate isAdditionalFlowStep(
    DataFlow::Node pred, DataFlow::Node succ, DataFlow::FlowLabel predlbl,
    DataFlow::FlowLabel succlbl
  ) {
    pred = entry and
    succ = exit and
    predlbl = startFlowLabel and
    succlbl = endFlowLabel
  }
}

private class AdditionalIndirectFlowThroughSummaryFromSpec extends DataFlow::Configuration {
  DataFlow::Node entry;

  string startFlowLabel;

  DataFlow::Node exit;

  string endFlowLabel;

  AdditionalIndirectFlowThroughSummaryFromSpec() {
    exists(
      Portal base, int i, ParameterPortal inparm, int j, ParameterPortal cbparm, int k,
      ParameterPortal outparm, DataFlow::InvokeNode invk, string config
    |
      additionalSteps(inparm.toString(), startFlowLabel, outparm.toString(), endFlowLabel, config) and
      configSpec(this, config) and
      base = inparm.getBasePortal() and
      i = inparm.getIndex() and
      cbparm = outparm.getBasePortal() and
      base = cbparm.getBasePortal() and
      j = cbparm.getIndex() and
      k = outparm.getIndex() and
      invk = base.getAnExitNode(_).getAnInvocation()
    |
      entry = invk.getArgument(i) and
      exit = invk.getCallback(j).getParameter(k)
    )
  }

  override predicate isAdditionalFlowStep(
    DataFlow::Node pred, DataFlow::Node succ, DataFlow::FlowLabel predlbl,
    DataFlow::FlowLabel succlbl
  ) {
    pred = entry and
    succ = exit and
    predlbl = startFlowLabel and
    succlbl = endFlowLabel
  }
}

/**
 * An additional flow step specified through the `additionalSteps` predicate.
 */
private class AdditionalFlowStepFromSpec extends DataFlow::Configuration {
  DataFlow::Node entry;

  string startFlowLabel;

  DataFlow::Node exit;

  string endFlowLabel;

  AdditionalFlowStepFromSpec() {
    exists(Portal startPortal, Portal endPortal, string config |
      additionalSteps(startPortal.toString(), startFlowLabel, endPortal.toString(), endFlowLabel,
        config) and
      configSpec(this, config) and
      not (
        startPortal instanceof ParameterPortal and
        (endPortal instanceof ReturnPortal or endPortal instanceof ParameterPortal)
      ) and
      entry = startPortal.getAnEntryNode(_) and
      exit = endPortal.getAnExitNode(_)
    )
  }

  override predicate isAdditionalFlowStep(
    DataFlow::Node pred, DataFlow::Node succ, DataFlow::FlowLabel predlbl,
    DataFlow::FlowLabel succlbl
  ) {
    pred = entry and
    succ = exit and
    predlbl = startFlowLabel and
    succlbl = endFlowLabel
  }
}
