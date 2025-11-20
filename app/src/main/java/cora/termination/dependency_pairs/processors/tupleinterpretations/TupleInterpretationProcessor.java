package cora.termination.dependency_pairs.processors.tupleinterpretations;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;
import java.util.TreeSet;
import java.util.Vector;
import java.util.function.BiConsumer;
import java.util.function.Consumer;

import org.checkerframework.checker.units.qual.t;

import charlie.parser.Parser.Tup;
import charlie.smt.Addition;
import charlie.smt.CMult;
import charlie.smt.Constraint;
import charlie.smt.IValue;
import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.Multiplication;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.smt.Valuation;
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
import cora.config.Settings;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.Processor;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;
import cora.termination.dependency_pairs.DP;

public class TupleInterpretationProcessor implements Processor {

  public static String queryDisabledCode() {
    return "tupleinterp";
  }

  @Override
  public boolean isApplicable(Problem dpp) {
    return !Settings.isDisabled(queryDisabledCode()) &&
        dpp.getOriginalTRS().verifyProperties(
            Level.FIRSTORDER, Constrained.NO,
            TypeLevel.SIMPLE, Lhs.PATTERN,
            Root.FUNCTION, FreshRight.NONE);
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
    Hashtable<Variable, IntegerExpression> variableIntegerExpressions
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
    // System.out.println("\t\t\tAdding coefficient: " + coefficientExpr.toString() + 
    //   " to variable expression: " + variableExpr.toString()
    // );
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
    Hashtable<Variable, IntegerExpression> variableIntegerExpressions
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
    Hashtable<Variable, IntegerExpression> variableIntegerExpressions,
    Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients
  ) {

    IntegerExpression multIdentity = SmtFactory.createValue(1);

    for (int childIndex = 1; childIndex <= addition.numChildren(); childIndex++) {
      IntegerExpression child = addition.queryChild(childIndex);

      // System.out.println("\t\t    Processing child: " + 
      //   child.toString() + " of type: " + child.getClass()
      // );

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
  private Addition simplifiedIterpertationForRule(
    Term lhs, Term rhs,
    SmtProblem problem, 
    Hashtable<FunctionSymbol, Vector<IntegerExpression>> symbolArgumentWeights,
    Hashtable<Variable, IntegerExpression> variableIntegerExpressions
  ) {
    IntegerExpression lhsCost = interpretTerm(
      lhs,
      problem,
      symbolArgumentWeights,
      variableIntegerExpressions
    );

    IntegerExpression rhsCost = interpretTerm(
      rhs,
      problem,
      symbolArgumentWeights,
      variableIntegerExpressions
    );

    // System.out.println(
    //   "Rule: " + lhs.toString() + " -> " + rhs.toString() +
    //   "\n\tinterpreted as: " + lhsCost.toString() + " >= " + rhsCost.toString()
    // );

    // Create constraint that lhsCost >= rhsCost -> lhsCost - rhsCost >= 0
    return (Addition) SmtFactory.createAddition(lhsCost, rhsCost.negate()).simplify();
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
      Hashtable<Variable, IntegerExpression> variableIntegerExpressions = new Hashtable<>();
      Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients = new Hashtable<>();

      Addition lhsMinusRhs = this.simplifiedIterpertationForRule(
        rule.queryLeftSide(), rule.queryRightSide(), 
        problem, symbolArgumentWeights, variableIntegerExpressions
      );

      System.out.println(
        "TupleInterpretationProcessor $ \n\tProcessing Rule: " + rule.toString() + 
        "\n\tinterpreted cost: " + lhsMinusRhs.toString());

      this.combineTermsOnVariables(lhsMinusRhs, variableIntegerExpressions, variableCoefficients);

      variableCoefficients.forEach((variableExpr, coefficientExpr) -> {
        Constraint constraint = SmtFactory.createGreater(
          SmtFactory.createAddition(coefficientExpr),
          SmtFactory.createValue(0)
        );
        System.out.println(
          "\t\tRequired by Rule " + constraint.toString() + 
          " for variable expression " + 
          (variableExpr.getClass() != IValue.class ? variableExpr.toString() : "constant part")
        );
        problem.require(constraint);
      });
    }
  
    Hashtable<DP, IVar> dpReductionIndicators = new Hashtable<>();

    for (DP dp : dpp.getDPList()) {
      Hashtable<Variable, IntegerExpression> variableIntegerExpressions = new Hashtable<>();
      Hashtable<IntegerExpression, List<IntegerExpression>> variableCoefficients = new Hashtable<>();

      Addition lhsMinusRhs = this.simplifiedIterpertationForRule(
        dp.lhs(), dp.rhs(), 
        problem, symbolArgumentWeights, variableIntegerExpressions
      );

      System.out.println("TupleInterpretationProcessor $ Processing DP: " + dp.toString());
      System.out.println("TupleInterpretationProcessor $ simplified cost: " + lhsMinusRhs.toString());

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
      
      IVar reductionIndicator = SmtFactory.createIntegerVariable(
        problem, 
        "dp_" + dp.lhs().queryRoot() + "->" + dp.rhs().queryRoot(),
         0, 1
      );
      dpReductionIndicators.put(dp, reductionIndicator);
      
      List<IntegerExpression> constant = variableCoefficients.getOrDefault(SmtFactory.createValue(1), new ArrayList<>());
      constant.add(SmtFactory.createAddition(SmtFactory.createValue(1), reductionIndicator.negate()));
      variableCoefficients.put(SmtFactory.createValue(1), constant);
      
      variableCoefficients.forEach((variableExpr, coefficientExpr) -> {
        Constraint constraint = SmtFactory.createGeq(SmtFactory.createAddition(coefficientExpr));
        System.out.println(
          "\t\tRequired by DP " + constraint.toString() + 
          " for variable expression " + 
          (variableExpr.getClass() != IValue.class ? variableExpr.toString() : "constant part")
        );
        problem.require(constraint);
      });
    }

    return switch (Settings.smtSolver.checkSatisfiability(problem)) {
      case Answer.YES(Valuation val) -> {

        TreeSet<Integer> indexOfOrientedDPs = new TreeSet<>();
        for (int dpIndex = 0; dpIndex < dpp.getDPList().size(); dpIndex++) {
          DP dp = dpp.getDPList().get(dpIndex);
          if (val.queryAssignment(dpReductionIndicators.get(dp)) == 0) {
            indexOfOrientedDPs.add(dpIndex); 
          }
        }

        List<IntegerExpression> interpetations = new ArrayList<>();

        // TODO: construct the actual interpretation functions per function symbol

        for (FunctionSymbol symbol : symbolArgumentWeights.keySet()) {
          symbolArgumentWeights.computeIfPresent(symbol, (key, argumentWeights) -> {
            Vector<IntegerExpression> evaluatedWeights = new Vector<>();
            argumentWeights.forEach(weight -> {
              evaluatedWeights.add(SmtFactory.createValue(val.queryAssignment((IVar) weight)));
            });
            return evaluatedWeights;
          });
        }

        yield new TupleInterpretationProofObject(dpp, indexOfOrientedDPs, interpetations);
      }

      case Answer.MAYBE(String reason) -> new TupleInterpretationProofObject(dpp, reason);

      case Answer.NO() -> new TupleInterpretationProofObject(dpp);
    };
  }
}