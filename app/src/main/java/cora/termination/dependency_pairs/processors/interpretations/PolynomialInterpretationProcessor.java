package cora.termination.dependency_pairs.processors.interpretations;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;
import java.util.TreeSet;
import java.util.Vector;

import charlie.smt.*;
import charlie.smt.SmtSolver.Answer;
import charlie.terms.FunctionSymbol;
import charlie.terms.Variable;
import charlie.trs.Rule;
import charlie.trs.TrsProperties.Constrained;
import charlie.trs.TrsProperties.FreshRight;
import charlie.trs.TrsProperties.Level;
import charlie.trs.TrsProperties.Lhs;
import charlie.trs.TrsProperties.Root;
import charlie.trs.TrsProperties.TypeLevel;
import charlie.util.Pair;
import cora.config.Settings;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.Processor;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;
import cora.termination.dependency_pairs.DP;

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
            Root.FUNCTION, FreshRight.NONE);
  }

  /**
   * Processes a dependency pair problem using tuple interpretations.
   * 
   * @param dpp The dependency pair problem to process.
   * @return A proof object representing the result of the processing.
   */
  @Override
  public ProcessorProofObject processDPP(Problem dpp) {

    Hashtable<Rule, Pair<IntegerExpression, IntegerExpression>> ruleInterpretations = new Hashtable<>();
    Hashtable<DP, Pair<IntegerExpression, IntegerExpression>> dpInterpretations = new Hashtable<>();
    Hashtable<FunctionSymbol, Vector<IntegerExpression>> symbolArgumentWeights = new Hashtable<>();
    List<IVar> allVariableIntegerExpressions = new ArrayList<>();
    Hashtable<DP, IVar> dpReductionIndicators = new Hashtable<>();
    SmtProblem problem = new SmtProblem();

    // Find all function symbols and create a cost function for them
    for (FunctionSymbol symbol : dpp.getOriginalTRS().queryAlphabet().getSymbols()) {
      if (symbol == null)
        throw new NullPointerException("FunctionSymbol is null");
      if (symbolArgumentWeights.containsKey(symbol)) {
        throw new IllegalStateException("Duplicate FunctionSymbol in TRS: " + symbol.queryName());
      }

      Vector<IntegerExpression> argumentWeights = new Vector<>();
      for (int i = 0; i < symbol.queryArity() + 1; i++) {
        argumentWeights.add(
            SmtFactory.createIntegerVariable(problem, symbol.queryName() + "_w" + i, 0, 10));
      }
      symbolArgumentWeights.put(symbol, argumentWeights);
    }

    // Create a generic cost function for each rewrite rule in the TRS
    for (Rule rule : dpp.getOriginalTRS().queryRules()) {
      Hashtable<Variable, IVar> variableIntegerExpressions = new Hashtable<>();
      Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients = new Hashtable<>();

      Pair<IntegerExpression, IntegerExpression> interpretationForRule = Interpretations.simplifiedIterpertationForRule(
          rule.queryLeftSide(), rule.queryRightSide(),
          problem, symbolArgumentWeights, variableIntegerExpressions);
      ruleInterpretations.put(rule, interpretationForRule);

      // Simplify lhsCost >= rhsCost to lhsCost - rhsCost >= 0
      Addition lhsMinusRhs = (Addition) SmtFactory.createAddition(
          interpretationForRule.left(),
          SmtFactory.createNegation(interpretationForRule.right())).simplify();

      Interpretations.combineTermsOnVariables(lhsMinusRhs, variableIntegerExpressions, variableCoefficients);

      allVariableIntegerExpressions.addAll(variableIntegerExpressions.values());

      // Require that each rule has a non-increasing interpretation
      variableCoefficients.forEach((variableExpr, coefficientExpr) -> {
        problem.require(SmtFactory.createGeq(SmtFactory.createAddition(coefficientExpr)));
      });

    }

    for (DP dp : dpp.getDPList()) {
      Hashtable<Variable, IVar> variableIntegerExpressions = new Hashtable<>();
      Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients = new Hashtable<>();

      Pair<IntegerExpression, IntegerExpression> interpretationForDP = Interpretations.simplifiedIterpertationForRule(
          dp.lhs(), dp.rhs(),
          problem, symbolArgumentWeights, variableIntegerExpressions);
      dpInterpretations.put(dp, interpretationForDP);

      Addition lhsMinusRhs = (Addition) SmtFactory.createAddition(
          interpretationForDP.left(),
          SmtFactory.createNegation(interpretationForDP.right())).simplify();

      Interpretations.combineTermsOnVariables(lhsMinusRhs, variableIntegerExpressions, variableCoefficients);

      /*
       * for DPs we require at least >= 0, but in order to reduce towards termination
       * we need > 0.
       * We want to reduce as many DPs as possible in each step.
       * Therefor we try to find as many strictly decreasing DPs as possible,
       * in order to do this we rewrite forinstance a + bx + cy >= 0 to the form of:
       * a-d + bx + cy >= 0, which is equivalent to a + bx + cy > 0 iff d=1.
       * but SMT-s generaly try to stick to a value of 0, so we rewrite the constraint
       * to:
       * (a + 1 - d) + bx + cy, with for d=0 : `> 0`, and for d=1: `>= 0`,
       * making sure the SMT levetates towards strictly decreasing interpretations.
       */

      // TODO: improve to constant part end up being > 0.
      // This removes the need for an indicator.

      IVar reductionIndicator = SmtFactory.createIntegerVariable(
          problem, dp.lhs().queryRoot() + "_red", 0, 1);
      dpReductionIndicators.put(dp, reductionIndicator);

      List<IntegerExpression> constants = variableCoefficients.getOrDefault(
          SmtFactory.createValue(1), new ArrayList<>());

      constants.add(SmtFactory.createAddition(SmtFactory.createValue(-1), reductionIndicator));
      variableCoefficients.put(SmtFactory.createValue(1), constants);

      allVariableIntegerExpressions.addAll(variableIntegerExpressions.values());
      variableCoefficients.forEach((variableExpr, coefficientExpr) -> {
        problem.require(SmtFactory.createGeq(SmtFactory.createAddition(coefficientExpr)));
      });
    }

    // Require that at least one DP is strictly decreasing
    problem.require(SmtFactory.createDisjunction(
        dpReductionIndicators.values().stream()
            .map((indicator) -> SmtFactory.createGreater(SmtFactory.createValue(1), indicator))
            .toList()));

    return switch (Settings.smtSolver.checkSatisfiability(problem)) {
      case Answer.YES(Valuation val) -> {

        // Determine which DPs are oriented
        TreeSet<Integer> indexOfOrientedDPs = new TreeSet<>();
        for (int dpIndex = 0; dpIndex < dpp.getDPList().size(); dpIndex++) {
          DP dp = dpp.getDPList().get(dpIndex);
          if (val.queryAssignment(dpReductionIndicators.get(dp)) == 0) {
            indexOfOrientedDPs.add(dpIndex);
          }
        }

        Hashtable<IVar, IntegerExpression> weightAssignments = new Hashtable<>();
        // For each function symbol, query and update the assigned weights
        for (FunctionSymbol symbol : symbolArgumentWeights.keySet()) {
          symbolArgumentWeights.computeIfPresent(symbol, (key, argumentWeights) -> {
            Vector<IntegerExpression> evaluatedWeights = new Vector<>();
            argumentWeights.forEach(weight -> {
              IntegerExpression evaluatedWeight = SmtFactory.createValue(val.queryAssignment((IVar) weight));
              evaluatedWeights.add(evaluatedWeight);
              weightAssignments.put((IVar) weight, evaluatedWeight);
            });
            return evaluatedWeights;
          });
        }

        Hashtable<Rule, Constraint> newRuleInterpretations = new Hashtable<>();
        ruleInterpretations.forEach((rule, pair) -> {
          newRuleInterpretations.put(rule, SmtFactory.createGeq(
              pair.left().substitute(weightAssignments).simplify(),
              pair.right().substitute(weightAssignments).simplify()));
        });

        Hashtable<DP, Pair<IntegerExpression, IntegerExpression>> newDpInterpretations = new Hashtable<>();
        dpInterpretations.forEach((dp, pair) -> {
          newDpInterpretations.put(dp, new Pair<>(
              pair.left().substitute(weightAssignments).simplify(),
              pair.right().substitute(weightAssignments).simplify()));
        });

        Hashtable<FunctionSymbol, IntegerExpression> costFunctions = new Hashtable<>();
        dpp.getOriginalTRS().queryAlphabet().getSymbols().forEach((functionSymbol) -> {
          Vector<IntegerExpression> weights = symbolArgumentWeights.get(functionSymbol);
          List<IntegerExpression> subterms = new ArrayList<>();
          subterms.add(weights.getFirst()); // constant term
          for (int argIndex = 0; argIndex < functionSymbol.queryArity(); argIndex++) {
            subterms.add(SmtFactory.createMultiplication(
                weights.get(argIndex + 1),
                SmtFactory.createIntegerVariable(problem, String.valueOf((char) ('a' + argIndex)), argIndex,
                    argIndex)));
          }
          costFunctions.put(functionSymbol, SmtFactory.createAddition(subterms));
        });

        yield new PolynomialInterpretationProofObject(
            dpp, indexOfOrientedDPs, costFunctions,
            newRuleInterpretations, newDpInterpretations);
      }

      case Answer.MAYBE(String reason) -> new PolynomialInterpretationProofObject(dpp, reason);

      case Answer.NO() -> new PolynomialInterpretationProofObject(dpp);
    };
  }
}