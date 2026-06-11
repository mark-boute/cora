package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import charlie.smt.Addition;
import charlie.smt.CMult;
import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.Multiplication;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.trs.Rule;
import charlie.util.Pair;

public class RuleTupleInterpretation {
  SmtProblem _problem;
  private final Term _left;
  private final Term _right;

  private final List<IntegerExpression> _leftSideInterpretation;
  private final List<IntegerExpression> _rightSideInterpretation;
  private final Map<Variable, List<IVar>> _variableMap = new HashMap<>();

  public RuleTupleInterpretation(SmtProblem problem, Term left, Term right,
      Map<FunctionSymbol, SymbolTupleInterpretation> symbolInterpretations
  ) {
    _problem = problem;
    _left = left;
    _right = right;
    int tupleSize = symbolInterpretations.values().iterator().next().getConfig().size();
    _leftSideInterpretation = interpretTerm(left, problem, tupleSize, symbolInterpretations);
    _rightSideInterpretation = interpretTerm(right, problem, tupleSize, symbolInterpretations);
  }

  public RuleTupleInterpretation(SmtProblem problem, Rule rule,
      Map<FunctionSymbol, SymbolTupleInterpretation> symbolInterpretations) {
    this(problem, rule.queryLeftSide(), rule.queryRightSide(), symbolInterpretations);
  }

  // public void requireWeaklyDecreasing() {
  //   // All IVars assigned to rule variables are the "parameters" —
  //   // the unknowns whose coefficients must be proven non-negative.
  //   List<IVar> parameterVariables = _variableMap.values().stream()
  //     .flatMap(List::stream)
  //     .collect(Collectors.toList());

  //   System.out.println("For rule: " + _left + " -> " + _right + "\n");

  //   for (int i = 0; i < _leftSideInterpretation.size(); i++) {
  //     System.out.println("\nComparing tuple element " + (i + 1) + ":");
  //     System.out.println(_leftSideInterpretation.get(i));
  //     System.out.println(">=");
  //     System.out.println(_rightSideInterpretation.get(i));

  //     IntegerExpression diff = SmtFactory.createAddition(
  //       _leftSideInterpretation.get(i),
  //       SmtFactory.createNegation(_rightSideInterpretation.get(i))
  //     ).simplify();

  //     System.out.println("\nSimplifies to:\n" + diff + "\n\n With requirements:\n");

  //     RuleTupleInterpretation.combineTermsOnParameterVariables(diff, parameterVariables)
  //         .values().stream()
  //         .map(SmtFactory::createGeq)
  //         .forEach(_problem::require);

  //     RuleTupleInterpretation.combineTermsOnParameterVariables(diff, parameterVariables)
  //         .values().stream()
  //         .map(SmtFactory::createGeq)
  //         .forEach(System.out::println);
  //   }
  // }

  public void requireWeaklyDecreasing() {
    List<IVar> parameterVariables = _variableMap.values().stream()
        .flatMap(List::stream)
        .collect(Collectors.toList());

    for (int i = 0; i < _leftSideInterpretation.size(); i++) {

      System.out.println("\nComparing tuple element " + (i + 1) + ":");
      System.out.println(_leftSideInterpretation.get(i));
      System.out.println(">=");
      System.out.println(_rightSideInterpretation.get(i));

      IntegerExpression diff = SmtFactory.createAddition(
        _leftSideInterpretation.get(i),
        SmtFactory.createNegation(_rightSideInterpretation.get(i))
      ).simplify();

      System.out.println("\nSimplifies to:\n" + diff + "\n\n With requirements:\n");

      Map<IntegerExpression, IntegerExpression> coeffMap =
        combineTermsOnParameterVariables(diff, parameterVariables);

      requireCoupledConstraints(coeffMap, parameterVariables);
    }
  }


  public List<IntegerExpression> getLeftSideInterpretation() {
    return _leftSideInterpretation;
  }

  public List<IntegerExpression> getRightSideInterpretation() {
    return _rightSideInterpretation;
  }

  public Map<Variable, List<IVar>> getVariableMap() {
    return _variableMap;
  }

  private List<IntegerExpression> interpretTerm(Term term, SmtProblem problem,
      int tupleSize, Map<FunctionSymbol, SymbolTupleInterpretation> symbolInterpretations) {

    if (term.isVariable()) {
      // computeIfAbsent guarantees x is the same List<IVar> on both sides
      return _variableMap.computeIfAbsent(term.queryVariable(), v -> {
        List<IVar> vars = new ArrayList<>();
        for (int i = 1; i <= tupleSize; i++)
          vars.add(SmtFactory.createIntegerVariable(
              problem, "_" + v.queryName() + "_" + i, 0, 10));
        return vars;
      }).stream().map(v -> (IntegerExpression) v).collect(Collectors.toList());
    }

    FunctionSymbol f = term.queryRoot();
    List<List<IntegerExpression>> argTuples = new ArrayList<>();
    for (int i = 1; i <= term.numberArguments(); i++)
      argTuples.add(interpretTerm(term.queryArgument(i), problem, tupleSize, symbolInterpretations));

    return symbolInterpretations.get(f).apply(argTuples);
  }

    /**
   * A helper function for using absolute positiveness in tuple interpretations.
   * Splits an addition into a list of IntegerExpressions that do not contain
   * variables.
   * e.g. for an addition c + abXY + dY, where XY and Y are variables in variableIntegerExpressions,
   * this method will return the map [1:c, XY:ab, Y:d].
   * @return A map from variable terms to their coefficient IntegerExpressions, and a separate entry for the constant part (with key multIdentity).
   */
  protected static Map<IntegerExpression, IntegerExpression> combineTermsOnParameterVariables(
            IntegerExpression difference, List<IVar> parameterVariables) {
    IntegerExpression one = SmtFactory.createValue(1);
    Map<IntegerExpression, IntegerExpression> coefficientsMap = new HashMap<>();

    List<IntegerExpression> children = (difference instanceof Addition add) 
        ? IntStream.rangeClosed(1, add.numChildren()).mapToObj(add::queryChild).toList()
        : List.of(difference);

    for (IntegerExpression child : children) {
      switch (child) {
        case IVar var: // single variable
          if (parameterVariables.contains(var)) {
            // Add 1 to the variable's coefficient
            addCoefficient(coefficientsMap, var, one);
          } else {
            // Add the child to the constant part
            addCoefficient(coefficientsMap, one, child);
          }
          break;
        case CMult cMult:
          if (cMult.queryChild() instanceof Multiplication mult) {

            Pair<List<IntegerExpression>, List<IntegerExpression>> split = splitMultiplicationChildren(
              mult, parameterVariables::contains
            );

            if (split.fst().isEmpty()) {
              addCoefficient(coefficientsMap, one, child);
            } else {
              // Prepend the outer CMult constant to the non-variable list
              split.snd().add(0, SmtFactory.createValue(cMult.queryConstant()));
              
              IntegerExpression combinedCoeff = SmtFactory.createMultiplication(split.snd()).simplify();
              IntegerExpression combinedVar = SmtFactory.createMultiplication(split.fst()).simplify();
              
              addCoefficient(coefficientsMap, combinedVar, combinedCoeff);
            }
          } else {
            IntegerExpression innerChild = cMult.queryChild();
            if (parameterVariables.contains(innerChild)) {
              addCoefficient(coefficientsMap, innerChild, SmtFactory.createValue(cMult.queryConstant()));
            } else {
              addCoefficient(coefficientsMap, one, child);
            }
          }
          break;

        case Multiplication mult:

          Pair<List<IntegerExpression>, List<IntegerExpression>> split = splitMultiplicationChildren(
            mult, parameterVariables::contains
          );

          if (split.fst().isEmpty()) {
            addCoefficient(coefficientsMap, one, child);
          } else {
            IntegerExpression combinedCoeff = SmtFactory.createMultiplication(split.snd()).simplify();
            IntegerExpression combinedVar = SmtFactory.createMultiplication(split.fst()).simplify();
            
            addCoefficient(coefficientsMap, combinedVar, combinedCoeff);
          }
          break;

        default:
          throw new IllegalStateException("Unexpected child type in combineTermsOnVariables: " + child.getClass());
      }
    }
  
    return coefficientsMap;
  }

  private static void addCoefficient(Map<IntegerExpression, IntegerExpression> map, IntegerExpression key, IntegerExpression valueToAdd) {
    map.compute(key, (k, existingCoeff) -> 
        (existingCoeff == null) ? valueToAdd 
                                : SmtFactory.createAddition(existingCoeff, valueToAdd).simplify()
    );
  }

  private static Pair<List<IntegerExpression>, List<IntegerExpression>> splitMultiplicationChildren(
    Multiplication mult, 
    Predicate<IntegerExpression> condition
  ) {
    Map<Boolean, List<IntegerExpression>> partitioned = IntStream.rangeClosed(1, mult.numChildren())
      .mapToObj(mult::queryChild)
      .collect(Collectors.partitioningBy(condition));

    return new Pair<>(partitioned.get(true), partitioned.get(false));
  }

  private void requireCoupledConstraints(Map<IntegerExpression, IntegerExpression> coeffMap, List<IVar> parameterVariables) {

    Set<IntegerExpression> absorbed = new HashSet<>();

    for (IVar v : parameterVariables) {
      IntegerExpression linearCoeff = coeffMap.get(v);
      if (linearCoeff == null) continue;

      Optional<Map.Entry<IntegerExpression, IntegerExpression>> squaredEntry =
        coeffMap.entrySet().stream()
                .filter(e -> isSquareOf(e.getKey(), v))
                .findFirst();

      // check if we have cx^2 + dx, and if so, require c >= 0 and c + d >= 0
      if (squaredEntry.isPresent()) {
        IntegerExpression c = squaredEntry.get().getValue();
        IntegerExpression d = linearCoeff;

        // c >= 0
        _problem.require(SmtFactory.createGeq(c));
        // c + d >= 0  (the coupled constraint)
        _problem.require(SmtFactory.createGeq(
            SmtFactory.createAddition(c, d).simplify()));

        // For debugging: print out the coupled constraints
        System.out.println("Coupled constraints for variable " + v + ":");
        System.out.println("  " + c + " >= 0");
        System.out.println("  " + c + " + " + d + " >= 0");

        absorbed.add(v);
        absorbed.add(squaredEntry.get().getKey());
      }
    }

    // Everything not absorbed gets the standard treatment
    coeffMap.entrySet().stream()
        .filter(e -> !absorbed.contains(e.getKey()))
        .map(Map.Entry::getValue)
        .map(SmtFactory::createGeq)
        .forEach(_problem::require);

    // For debugging: print out any remaining constraints
    coeffMap.entrySet().stream()
        .filter(e -> !absorbed.contains(e.getKey()))
        .forEach(e -> System.out.println("Remaining constraint: " + e.getValue() + " >= 0"));
}

// Reference equality on IVar is intentional: these are the exact same
// objects placed in the expression by interpretTerm
private static boolean isSquareOf(IntegerExpression expr, IVar v) {
    if (!(expr instanceof Multiplication mult)) return false;
    if (mult.numChildren() != 2) return false;
    return mult.queryChild(1) == v && mult.queryChild(2) == v;
}
    // public Pair<IntegerExpression, IntegerExpression> substitution(Map<IVar, IntegerExpression> variableAssignments) {
    // return new Pair<>(
    //   _leftSideInterpretation.substitute(variableAssignments).simplify(),
    //   _rightSideInterpretation.substitute(variableAssignments).simplify()
    // );
}
