package cora.termination.dependency_pairs.processors.tupleinterpretations;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;
import java.util.TreeSet;
import java.util.Vector;

import charlie.smt.*;
import charlie.smt.SmtSolver.Answer;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
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

public class TupleInterpretationProcessor implements Processor {

  private Hashtable<Rule, Pair<IntegerExpression, IntegerExpression>> _ruleInterpretations = new Hashtable<>();
  private Hashtable<DP, Pair<IntegerExpression, IntegerExpression>> _dpInterpretations = new Hashtable<>();
  private List<IVar> _allVariableIntegerExpressions = new ArrayList<>();
  private Hashtable<DP, IVar> _dpReductionIndicators = new Hashtable<>();

  /**
   * Allow this processor to be disabled via settings.
   * 
   * @return The disabled code string.
   */
  public static String queryDisabledCode() {
    return "tupleinterp";
  }

  /**
   * Checks whether this processor is applicable to the given dependency pair problem.
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
   * Recursively compute the cost of a term.
   * 
   * @param term The term to interpret.
   * @param problem The SMT problem to which variables will be added.
   * @param symbolArgumentWeights The mapping of function symbols to their argument weights.
   * @param variableIntegerExpressions The mapping of variables to their IntegerExpressions.
   * 
   * @return The IntegerExpression representing the cost of the term.
   */
  private IntegerExpression interpretTerm(
    Term term, 
    SmtProblem problem, 
    Hashtable<FunctionSymbol, Vector<IntegerExpression>> symbolArgumentWeights,
    Hashtable<Variable, IVar> variableIntegerExpressions
  ) {

    if (term.isVariable()) {  // Term root is a free (unsatisfied) variable
      variableIntegerExpressions.putIfAbsent(
        term.queryVariable(), 
        SmtFactory.createIntegerVariable(
          problem, term.queryVariable().queryName(), 0, 1000
        )
      );

      // return variable's associated cost expression
      return variableIntegerExpressions.get(term.queryVariable());
    }

    // Term is a function term.
    Vector<IntegerExpression> argumentWeights = symbolArgumentWeights.get(term.queryRoot());

    List<IntegerExpression> subtermCosts = new ArrayList<>(argumentWeights.size());
    subtermCosts.add(argumentWeights.getFirst()); // constant term

    for (int i = 0; i < term.numberArguments(); i++) {

      IntegerExpression innerExpression = interpretTerm(
        term.queryArguments().get(i), 
        problem, 
        symbolArgumentWeights, 
        variableIntegerExpressions
      );

      subtermCosts.add(SmtFactory.createMultiplication(argumentWeights.get(i + 1), innerExpression));
    }
  
    // simplify the addition of all subterm costs and return,
    // if a term is simplified any later simplification calls will be constant time.
    return SmtFactory.createAddition(subtermCosts).simplify();
  }

  /**
   * Adds a coefficient expression to the list of coefficients for a variable expression.
   * 
   * @param variableCoefficients The hashtable mapping variable expressions to their coefficient lists.
   * @param coefficientExpr The coefficient expression to add.
   * @param variableExpr The variable expression to which the coefficient belongs.
   */
  private void addCoefficientToVarList(
    Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients,
    IntegerExpression coefficientExpr,
    IntegerExpression variableExpr
  ) {
    variableCoefficients.putIfAbsent(variableExpr, new ArrayList<IntegerExpression>());
    variableCoefficients.get(variableExpr).add(coefficientExpr);
  }

  /**
   * Helper function for splitting a multiplication into variable and non-variable parts.
   * @param multiplication
   * @param nonVariablesInChildExpressionOut
   * @param variableInChildExpressionOut
   * @param variableIntegerExpressions
   */
  private void splitMultiplicationOnVariables(
    Multiplication multiplication,
    List<IntegerExpression> nonVariablesInChildExpressionOut,
    List<IntegerExpression> variableInChildExpressionOut,
    Hashtable<Variable, IVar> variableIntegerExpressions
  ) {
    for (int multChild = 1; multChild <= multiplication.numChildren(); multChild++) {
      IntegerExpression multiplicationChild = multiplication.queryChild(multChild);
      if (variableIntegerExpressions.containsValue(multiplicationChild)) {
        variableInChildExpressionOut.add(multiplicationChild);
      } else {
        nonVariablesInChildExpressionOut.add(multiplicationChild);
      }
    }
  }

  /**
   * A helper function for using absolute positiveness in tuple interpretations.
   * Splits an addition into a list of IntegerExpressions that do not contain variables.
   * e.g. for an addition c + abXY + dY, where XY and Y are variables in variableIntegerExpressions,
   * this method will return the list [c, ab, d].
   * 
   * @param addition The addition to split.
   * @param variableIntegerExpressions The mapping of variables to IntegerExpressions.
   * @return A list of IntegerExpressions that do not contain variables.
   */
  private void combineTermsOnVariables(
    Addition addition,
    Hashtable<Variable, IVar> variableIntegerExpressions,
    Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients
  ) {

    IntegerExpression multIdentity = SmtFactory.createValue(1);

    for (int childIndex = 1; childIndex <= addition.numChildren(); childIndex++) {
      IntegerExpression child = addition.queryChild(childIndex);

      switch (child) {
        case IVar var: // single variable
          if (variableIntegerExpressions.containsValue(var)) {
            // add 1 as coefficient to variable's coefficient list
            addCoefficientToVarList(variableCoefficients, multIdentity, var);
          } else {
            // add constant as part of the constant part
            addCoefficientToVarList(variableCoefficients, var, multIdentity);
          }
          break;

        case CMult cMult: // multiplication by a constant may also be a negated term
          if (cMult.queryChild() instanceof Multiplication mult) {
            // cMult is a wrapped multiplication
            List<IntegerExpression> nonVariablesInChildExpression = new ArrayList<>();
            List<IntegerExpression> variableInChildExpression = new ArrayList<>();
            this.splitMultiplicationOnVariables(
              mult, nonVariablesInChildExpression, 
              variableInChildExpression, variableIntegerExpressions
            );

            // if mult has no variables (e.g. -(C0 * C1)), add to constant part
            if (variableInChildExpression.size() == 0) { 
              addCoefficientToVarList(variableCoefficients, child, multIdentity);
              break;
            }

            // if mult has variables (e.g. -(C * V)), add coefficient (-C) to variable V's list
            addCoefficientToVarList(variableCoefficients, 
              SmtFactory.createMultiplication(
                cMult.queryConstant(), SmtFactory.createMultiplication(nonVariablesInChildExpression)
              ).simplify(), 
              SmtFactory.createMultiplication(variableInChildExpression)
            );
          } else {
            // cMult is a simple multiplication on a constant (e.g. -cC), 
            // so we add it to the constant part
            if (!variableIntegerExpressions.containsValue(cMult.queryChild())) {
              addCoefficientToVarList(variableCoefficients, cMult, multIdentity);
              break;
            }

            // cMult is a multiplication on a variable (i.e. cV), 
            // so we add the integer c to V's coefficient list
            addCoefficientToVarList(variableCoefficients, 
              SmtFactory.createValue(cMult.queryConstant()),
              cMult.queryChild()
            );
          }
          break;
      
        case Multiplication mult:
          List<IntegerExpression> nonVariablesInChildExpression = new ArrayList<>();
          List<IntegerExpression> variableInChildExpression = new ArrayList<>();
          this.splitMultiplicationOnVariables(
            mult, nonVariablesInChildExpression, 
            variableInChildExpression, variableIntegerExpressions
          );

          if (variableInChildExpression.size() == 0) {
            addCoefficientToVarList(variableCoefficients, child, multIdentity);
            break;
          }

          addCoefficientToVarList(variableCoefficients, 
            SmtFactory.createMultiplication(nonVariablesInChildExpression), 
            SmtFactory.createMultiplication(variableInChildExpression)
          );
          break;

        default:
          throw new IllegalStateException(
            "Unexpected child type in combineTermsOnVariables: " + child.getClass()
          );
      }
    }
  }

  /**
   * Creates a simplified interpretation for a rule lhs -> rhs as an Addition
   * represented as: lhsCost - rhsCost in a simplified form.
   * 
   * @param lhs The left hand side term of the rule.
   * @param rhs The right hand side term of the rule.
   * @param problem The SMT problem to which variables will be added.
   * @param symbolArgumentWeights The mapping of function symbols to their argument weights.
   * @param variableIntegerExpressions The mapping of variables to their IntegerExpressions.
   * 
   * @return Simplified addition representing lhsCost - rhsCost
   */
  private Pair<IntegerExpression, IntegerExpression> simplifiedIterpertationForRule(
    Term lhs, Term rhs,
    SmtProblem problem, 
    Hashtable<FunctionSymbol, Vector<IntegerExpression>> symbolArgumentWeights,
    Hashtable<Variable, IVar> variableIntegerExpressions
  ) {
    System.out.println("intps");
    IntegerExpression lhsCost = interpretTerm(
      lhs, problem, symbolArgumentWeights, variableIntegerExpressions
    );

    IntegerExpression rhsCost = interpretTerm(
      rhs, problem, symbolArgumentWeights, variableIntegerExpressions
    );

    System.out.println("done intps");

    // Create constraint that lhsCost >= rhsCost -> lhsCost - rhsCost >= 0
    return new Pair<IntegerExpression, IntegerExpression>(lhsCost, rhsCost);
  }

  // TODO: THIS SHOULD PROBABLY BE ADDED TO INTEGEREXPRESSION
  /**
   * Partially evaluates an IntegerExpression by substituting variable values from the valuation.
   * 
   * @param expression The IntegerExpression to partially evaluate.
   * @param valuation The valuation containing variable assignments for non-free variables.
   * @return The partially evaluated IntegerExpression.
   */
  private IntegerExpression partialEvalIntegerExpression(
    IntegerExpression expression,
    Valuation valuation
  ) {
    switch (expression) {
      case IVar var -> { // base case: variable or coefficient
        if (_allVariableIntegerExpressions.contains(var)) {
          return var;
        }
        return SmtFactory.createValue(valuation.queryAssignment(var));
      }

      case Addition addition -> {
        List<IntegerExpression> evaluatedChildren = new ArrayList<>();
        for (int i = 1; i <= addition.numChildren(); i++) {
          evaluatedChildren.add(
            this.partialEvalIntegerExpression(addition.queryChild(i), valuation)
          );
        }
        return SmtFactory.createAddition(evaluatedChildren);
      }

      case CMult cMult -> {
        return SmtFactory.createMultiplication(
          cMult.queryConstant(),
          this.partialEvalIntegerExpression(cMult.queryChild(), valuation)
        );
      }

      case Multiplication mult -> {
        List<IntegerExpression> evaluatedChildren = new ArrayList<>();
        for (int i = 1; i <= mult.numChildren(); i++) {
          evaluatedChildren.add(
            this.partialEvalIntegerExpression(mult.queryChild(i), valuation)
          );
        }
        return SmtFactory.createMultiplication(evaluatedChildren);
      }

      default -> {
        throw new IllegalStateException(
          "Unexpected IntegerExpression type in partialEvalIntegerExpression: " + 
          expression.getClass()
        );
      }
    }
  }

  /**
   * Processes a dependency pair problem using tuple interpretations.
   * 
   * @param dpp The dependency pair problem to process.
   * @return A proof object representing the result of the processing. 
   */
  @Override
  public ProcessorProofObject processDPP(Problem dpp) {

    SmtProblem problem = new SmtProblem();
    Hashtable<FunctionSymbol, Vector<IntegerExpression>> symbolArgumentWeights = new Hashtable<>();

    // Find all function symbols and create a cost function for them
    for (FunctionSymbol symbol : dpp.getOriginalTRS().queryAlphabet().getSymbols()) {
      if (symbol == null) throw new NullPointerException("FunctionSymbol is null");
      if (symbolArgumentWeights.containsKey(symbol)) {
        throw new IllegalStateException("Duplicate FunctionSymbol in TRS: " + symbol.queryName());
      }

      Vector<IntegerExpression> argumentWeights = new Vector<>();
      for (int i = 0; i < symbol.queryArity() + 1; i++) {
        argumentWeights.add(
          SmtFactory.createIntegerVariable(problem, symbol.queryName() + "_w" + i, 0,1000)
        );
      }
      symbolArgumentWeights.put(symbol, argumentWeights);
    }

    // Create a generic cost function for each rewrite rule in the TRS
    for (Rule rule : dpp.getOriginalTRS().queryRules()) {
      Hashtable<Variable, IVar> variableIntegerExpressions = new Hashtable<>();
      Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients = new Hashtable<>();

      Pair<IntegerExpression, IntegerExpression> interpretationForRule = this.simplifiedIterpertationForRule(
        rule.queryLeftSide(), rule.queryRightSide(), 
        problem, symbolArgumentWeights, variableIntegerExpressions
      );
      _ruleInterpretations.put(rule, interpretationForRule);

      // Simplify lhsCost >= rhsCost to lhsCost - rhsCost >= 0
      Addition lhsMinusRhs = (Addition) SmtFactory.createAddition(
        interpretationForRule.left(),
        SmtFactory.createNegation(interpretationForRule.right())
      ).simplify();

      this.combineTermsOnVariables(lhsMinusRhs, variableIntegerExpressions, variableCoefficients);

      _allVariableIntegerExpressions.addAll(variableIntegerExpressions.values());

      // Require that each rule has a non-increasing interpretation
      variableCoefficients.forEach((variableExpr, coefficientExpr) -> {
        problem.require(SmtFactory.createGeq(SmtFactory.createAddition(coefficientExpr)));
      });

    }

    for (DP dp : dpp.getDPList()) {
      Hashtable<Variable, IVar> variableIntegerExpressions = new Hashtable<>();
      Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients = new Hashtable<>();

      Pair<IntegerExpression, IntegerExpression> interpretationForDP = this.simplifiedIterpertationForRule(
        dp.lhs(), dp.rhs(), 
        problem, symbolArgumentWeights, variableIntegerExpressions
      );
      _dpInterpretations.put(dp, interpretationForDP);

      Addition lhsMinusRhs = (Addition) SmtFactory.createAddition(
        interpretationForDP.left(),
        SmtFactory.createNegation(interpretationForDP.right())
      ).simplify();

      this.combineTermsOnVariables(lhsMinusRhs, variableIntegerExpressions, variableCoefficients);

      /*
        for DPs we require at least >= 0, but in order to reduce towards termination we need > 0.
        We want to reduce as many DPs as possible in each step.
        Therefor we try to find as many strictly decreasing DPs as possible,
        in order to do this we rewrite forinstance a + bx + cy >= 0 to the form of:
        a-d + bx + cy >= 0, which is equivalent to a + bx + cy > 0 iff d=1.
        but SMT-s generaly try to stick to a value of 0, so we rewrite the constraint to:
        (a + 1 - d) + bx + cy, with for d=0 : `> 0`, and for d=1: `>= 0`, 
        making sure the SMT levetates towards strictly decreasing interpretations.        
      */
      
      System.out.println("Creating indicator");

      IVar reductionIndicator = SmtFactory.createIntegerVariable(
        problem, dp.lhs().queryRoot() + "_red", 0, 1
      );
      _dpReductionIndicators.put(dp, reductionIndicator);
      
      List<IntegerExpression> constants = variableCoefficients.getOrDefault(
        SmtFactory.createValue(1), new ArrayList<>()
      );

      constants.add(SmtFactory.createAddition(SmtFactory.createValue(-1), reductionIndicator));
      variableCoefficients.put(SmtFactory.createValue(1), constants);
      
      System.out.println("req loop over variableCoefficients");

      _allVariableIntegerExpressions.addAll(variableIntegerExpressions.values());
      variableCoefficients.forEach((variableExpr, coefficientExpr) -> {
        problem.require(SmtFactory.createGeq(SmtFactory.createAddition(coefficientExpr)));
      });
    }

    // Require that at least one DP is strictly decreasing
    problem.require(SmtFactory.createDisjunction(
      _dpReductionIndicators.values().stream()
        .map((indicator) -> SmtFactory.createGreater(SmtFactory.createValue(1), indicator))
        .toList()
    ));

    return switch (Settings.smtSolver.checkSatisfiability(problem)) {
      case Answer.YES(Valuation val) -> {

        // Determine which DPs are oriented
        TreeSet<Integer> indexOfOrientedDPs = new TreeSet<>();
        for (int dpIndex = 0; dpIndex < dpp.getDPList().size(); dpIndex++) {
          DP dp = dpp.getDPList().get(dpIndex);
          if (val.queryAssignment(_dpReductionIndicators.get(dp)) == 0) {
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

        Hashtable<Rule, Constraint> ruleInterpretations = new Hashtable<>();
        _ruleInterpretations.forEach((rule, pair) -> {
          ruleInterpretations.put(rule, SmtFactory.createGeq(
            pair.left().substitute(weightAssignments).simplify(),
            pair.right().substitute(weightAssignments).simplify()
          ));
        });
      
        Hashtable<DP, Pair<IntegerExpression, IntegerExpression>> dpInterpretations = new Hashtable<>();
        _dpInterpretations.forEach((dp, pair) -> {
          dpInterpretations.put(dp, new Pair<>(
            pair.left().substitute(weightAssignments).simplify(),
            pair.right().substitute(weightAssignments).simplify()
          ));
        });

        Hashtable<FunctionSymbol, IntegerExpression> costFunctions = new Hashtable<>();
        dpp.getOriginalTRS().queryAlphabet().getSymbols().forEach((functionSymbol) -> {
          Vector<IntegerExpression> weights = symbolArgumentWeights.get(functionSymbol);
          List<IntegerExpression> subterms = new ArrayList<>();
          subterms.add(weights.getFirst()); // constant term
          for (int argIndex = 0; argIndex < functionSymbol.queryArity(); argIndex++) {
            subterms.add(SmtFactory.createMultiplication(
              weights.get(argIndex + 1), 
              SmtFactory.createIntegerVariable(problem, String.valueOf((char) ('a' + argIndex)), argIndex, argIndex)
            ));
          }
          costFunctions.put(functionSymbol, SmtFactory.createAddition(subterms));
        });

        yield new TupleInterpretationProofObject(
          dpp, indexOfOrientedDPs, costFunctions, 
          ruleInterpretations, dpInterpretations
        );
      }

      case Answer.MAYBE(String reason) -> new TupleInterpretationProofObject(dpp, reason);

      case Answer.NO() -> new TupleInterpretationProofObject(dpp);
    };
  }
}