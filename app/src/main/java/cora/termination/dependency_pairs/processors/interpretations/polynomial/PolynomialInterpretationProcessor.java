// 
package cora.termination.dependency_pairs.processors.interpretations.polynomial;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import charlie.smt.Constraint;
import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.smt.SmtSolver.Answer;
import charlie.smt.Valuation;
import charlie.terms.FunctionSymbol;
import charlie.trs.Rule;
import charlie.trs.TrsProperties.Constrained;
import charlie.trs.TrsProperties.FreshRight;
import charlie.trs.TrsProperties.Level;
import charlie.trs.TrsProperties.Lhs;
import charlie.trs.TrsProperties.Root;
import charlie.trs.TrsProperties.TypeLevel;
import charlie.util.Pair;
import cora.config.Settings;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.Processor;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

public class PolynomialInterpretationProcessor implements Processor {
    
  /**
   * Allow this processor to be disabled via settings.
   * 
   * @return The disabled code string.
   */
  public static String queryDisabledCode() {
    return "polynomialinterp";
  }

  /**
   * Checks whether this processor is applicable to the given dependency pair
   * problem.
   * 
   * @param dpp The dependency pair problem to check.
   * @return True if the processor is applicable, false otherwise.
   */
  @Override
  public boolean isApplicable(Problem dpp) {
    return !Settings.isDisabled(queryDisabledCode()) &&
      dpp.getOriginalTRS().verifyProperties(
        Level.FIRSTORDER, Constrained.NO,
        TypeLevel.SIMPLE, Lhs.PATTERN,
        Root.FUNCTION, FreshRight.NONE
      );
  }

  /**
   * Processes a dependency pair problem using polynomial interpretations.
   * 
   * @param dpp The dependency pair problem to process.
   * @return A proof object representing the result of the processing.
   */
  @Override
  public ProcessorProofObject processDPP(Problem dpp) {

    SmtProblem problem = new SmtProblem();

    // Create symbol interpretations for all function symbols in the original TRS.
    Map<FunctionSymbol, SymbolInterpretation> functionInterpretations = dpp.getOriginalTRS()
      .queryAlphabet().getSymbols().stream().collect(Collectors.toMap(
        symbol -> symbol,
        symbol -> new SymbolInterpretation(problem, symbol)
      ));

    // We use a singular TermInterpreter to collect all the IVar parameter variables for later assignment.
    TermInterpreter interpreter = new TermInterpreter(problem, functionInterpretations);

    // Interpret rules using the symbol interpretations, and add the weakly decreasing constraints to the SMT problem.
    Map<Rule, RuleInterpretation> ruleInterpretations = dpp.getOriginalTRS()
      .queryRules().stream().collect(Collectors.toMap(
        rule -> rule,
        rule -> new RuleInterpretation(rule, interpreter)
      ));
    ruleInterpretations.values().forEach(ri -> ri.requireWeaklyDecreasing(problem));

    // Interpret Dependency Pairs (DPs) and add reduction indicators for strictness in reduction.
    Map<DP, DependencyPairInterpretation> dpInterpretations = dpp.getDPList().stream()
      .collect(Collectors.toMap(
        dp -> dp,
        dp -> new DependencyPairInterpretation(dp, interpreter, problem),
        (existing, replacement) -> existing 
        // Duplicates may exist, but we should only interpret them once. 
        // In the justification we should still display both DPs.
      ));
    dpInterpretations.values().forEach(dpi -> dpi.requireWeaklyDecreasing(problem));

    // Progress constraint: Require that at least one DP is strictly decreasing (reduction indicator < 1, so 0)
    problem.require(SmtFactory.createDisjunction(
      dpInterpretations.values().stream()
        .map(dpi -> SmtFactory.createGreater(SmtFactory.createValue(1), dpi.queryReductionIndicator()))
        .toList()
    )); 

    return switch (Settings.smtSolver.checkSatisfiability(problem)) {
      case Answer.YES(Valuation val) -> {
        TreeSet<Integer> indexOfOrientedDPs = collectOrientedDpIndices(dpp.getDPList(), dpInterpretations, val);

        Map<IVar, IntegerExpression> weightAssignments = extractWeightAssignments(functionInterpretations.values(), val);

        yield new PolynomialInterpretationProofObject(
          dpp, 
          indexOfOrientedDPs, 
          evaluateCostFunctions(functionInterpretations, weightAssignments),
          evaluateRuleInterpretations(ruleInterpretations, weightAssignments), 
          evaluateDpInterpretations(dpInterpretations, weightAssignments)
        );
      }

      case Answer.MAYBE(String reason) -> new PolynomialInterpretationProofObject(dpp, reason);

      case Answer.NO() -> new PolynomialInterpretationProofObject(dpp);
    };
  }

  // --- Helper Methods ---

  private TreeSet<Integer> collectOrientedDpIndices(
    List<DP> dpList, 
    Map<DP, DependencyPairInterpretation> dpInterpretations, 
    Valuation val
  ) {
    return IntStream.range(0, dpList.size())
      .filter(idx -> val.queryAssignment(dpInterpretations.get(dpList.get(idx)).queryReductionIndicator()) == 0)
      .boxed()
      .collect(Collectors.toCollection(TreeSet::new));
  }

  private Map<IVar, IntegerExpression> extractWeightAssignments(
    java.util.Collection<SymbolInterpretation> interpretations, 
    Valuation val
  ) {
    Map<IVar, IntegerExpression> weightAssignments = new HashMap<>();
    interpretations.forEach(si -> si.getLinearCoefficients().forEach(weight -> {
      if (weight instanceof IVar var) {
        weightAssignments.put(var, SmtFactory.createValue(val.queryAssignment(var)));
      }
    }));
    return weightAssignments;
  }

  private Map<Rule, Constraint> evaluateRuleInterpretations(
    Map<Rule, RuleInterpretation> ruleInterpretations, 
    Map<IVar, IntegerExpression> weightAssignments
  ) {
    return ruleInterpretations.entrySet().stream().collect(Collectors.toMap(
      Map.Entry::getKey,
      entry -> SmtFactory.createGeq(
        entry.getValue().queryLeftSideInterpretation().substitute(weightAssignments),
        entry.getValue().queryRightSideInterpretation().substitute(weightAssignments)
      )
    ));
  }

  private Map<DP, Pair<IntegerExpression, IntegerExpression>> evaluateDpInterpretations(
    Map<DP, DependencyPairInterpretation> dpInterpretations, 
    Map<IVar, IntegerExpression> weightAssignments
  ) {
    return dpInterpretations.entrySet().stream().collect(Collectors.toMap(
      Map.Entry::getKey,
      entry -> entry.getValue().substitution(weightAssignments)
    ));
  }

  private Map<FunctionSymbol, IntegerExpression> evaluateCostFunctions(
    Map<FunctionSymbol, SymbolInterpretation> functionInterpretations, 
    Map<IVar, IntegerExpression> weightAssignments
  ) {
    return functionInterpretations.entrySet().stream().collect(Collectors.toMap(
      Map.Entry::getKey,
      entry -> entry.getValue().queryLinearCostFunction().substitute(weightAssignments)
    ));
  }
}