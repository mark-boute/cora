package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import charlie.smt.IExpPrinter;
import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;

import charlie.terms.FunctionSymbol;

public class SymbolTupleInterpretation {

  private final List<Function<List<List<IntegerExpression>>, IntegerExpression>> _polynomialFunctions;

  private final List<List<IVar>> _argumentVariables;
  private final List<List<IVar>> _coefficientVariables;
  private final TupleConfiguration _config;
  private final FunctionSymbol _symbol;

  private SymbolTupleInterpretation(
      List<Function<List<List<IntegerExpression>>, IntegerExpression>> polynomialFunctions,
      List<List<IVar>> argumentVariables,
      List<List<IVar>> coefficientVariables,
      TupleConfiguration config,
      FunctionSymbol symbol) {

    _polynomialFunctions = polynomialFunctions;
    _argumentVariables = argumentVariables;
    _coefficientVariables = coefficientVariables;
    _config = config;
    _symbol = symbol;
  }

  public List<IntegerExpression> apply(List<List<IntegerExpression>> argumentTuples) {
    return _polynomialFunctions.stream()
        .map(f -> f.apply(argumentTuples))
        .collect(Collectors.toList());
  }

  public List<IntegerExpression> getTuple() {
    int arity = _symbol.queryArity();
    List<List<IntegerExpression>> transposed = new ArrayList<>();
    for (int argIndex = 0; argIndex < arity; argIndex++) {
      List<IntegerExpression> argTuple = new ArrayList<>();
      for (int tupleIndex = 0; tupleIndex < _config.size(); tupleIndex++) {
        argTuple.add(_argumentVariables.get(tupleIndex).get(argIndex));
      }
      transposed.add(argTuple);
    }
    return apply(transposed);
  }

  public List<List<IVar>> getArgumentVariables() {
    return _argumentVariables;
  }

  public List<List<IVar>> queryCoefficients() {
    return _coefficientVariables;
  }

  public TupleConfiguration getConfig() {
    return _config;
  }

  public List<String> toEvaluatedStrings(Map<IVar, IntegerExpression> valuation) {
    IExpPrinter iExpPrinter = new IExpPrinter();
    return this.getTuple().stream()
        .map(expr -> iExpPrinter.print(expr.substitute(valuation).simplify())).toList();
  }

  public static class Builder {
    private final SmtProblem _problem;
    private final FunctionSymbol _symbol;
    private final TupleConfiguration _config;
    private final List<List<IVar>> _argumentVariables;
    private final List<List<IVar>> _coefficientVariables;

    public Builder(SmtProblem problem, FunctionSymbol symbol, TupleConfiguration config) {
      if (config.size() < 1)
        throw new IllegalArgumentException("Tuple length must be at least 1");

      _problem = problem;
      _symbol = symbol;
      _config = config;
      _argumentVariables = createArgumentVariables();
      _coefficientVariables = new ArrayList<>(); // We create coefficient variables on demand when building the
                                                 // polynomial functions
    }

    public SymbolTupleInterpretation build() {

      List<Function<List<List<IntegerExpression>>, IntegerExpression>> functions = new ArrayList<>(_config.size());

      for (int tupleIndex = 0; tupleIndex < _config.size(); tupleIndex++) {
        PolynomialConfiguration functionConfig = _config.get(tupleIndex);
        List<Function<List<List<IntegerExpression>>, IntegerExpression>> function = new ArrayList<>();

        // Edge case: we might interpret a constant, but not have a constant part in the
        // configuration.
        // In that case, we add a constant 0 to ensure the tuple element is not empty.
        if (_symbol.queryArity() == 0 && !functionConfig.has(PolynomialPart.CONSTANT))
          function.add(args -> SmtFactory.createValue(0));

        if (functionConfig.has(PolynomialPart.CONSTANT))
          function.add(buildConstantFunction(tupleIndex + 1));
        if (functionConfig.has(PolynomialPart.LINEAR))
          function.add(buildLinearFunction(tupleIndex + 1));
        if (functionConfig.has(PolynomialPart.SQUARED))
          function.add(buildSquaredFunction(tupleIndex + 1));
        if (functionConfig.has(PolynomialPart.INTERACTIONS))
          function.add(buildInteractionsFunction(tupleIndex + 1));

        functions.add(args -> SmtFactory.createAddition(
            function.stream().map(f -> f.apply(args)).collect(Collectors.toList())).simplify());
      }

      return new SymbolTupleInterpretation(functions, _argumentVariables, _coefficientVariables, _config, _symbol);
    }

    private List<List<IVar>> createArgumentVariables() {
      // Argument variables are shared throughout the tuple, we create them once here.
      // They have the shape: xn_i; n is the argument index, i is the tuple index.
      List<List<IVar>> argumentVariables = new ArrayList<>();

      for (int tupleIndex = 1; tupleIndex <= _config.size(); tupleIndex++) {
        List<IVar> argVariablesForArg = new ArrayList<>();
        for (int argIndex = 1; argIndex <= _symbol.queryArity(); argIndex++) {
          IVar argVariable = SmtFactory.createIntegerVariable(
              _problem,
              "x" + String.valueOf(argIndex) + "_" + String.valueOf(tupleIndex),
              0, 10);
          argVariablesForArg.add(argVariable);
        }
        argumentVariables.add(argVariablesForArg);
      }

      return argumentVariables;
    }

    private record ArgPosition(int argIndex, int argTupleIndex) {
    }

    private List<ArgPosition> allArgumentPositions() {
      List<ArgPosition> positions = new ArrayList<>();
      for (int argIndex = 0; argIndex < _symbol.queryArity(); argIndex++)
        for (int argTupleIndex = 0; argTupleIndex < _config.size(); argTupleIndex++)
          positions.add(new ArgPosition(argIndex, argTupleIndex));
      return positions;
    }

    private String positionSuffix(ArgPosition pos) {
      return "_x" + (pos.argIndex() + 1) + "_" + (pos.argTupleIndex() + 1);
    }

    private Function<List<List<IntegerExpression>>, IntegerExpression> buildPolynomialFunction(
        int tupleIndex,
        List<List<ArgPosition>> monomials,
        Function<List<ArgPosition>, String> nameSuffixForMonomial) {

      // One fresh coefficient per monomial, captured in the closure
      List<IVar> coefficients = monomials.stream()
          .map(monomial -> SmtFactory.createIntegerVariable(
              _problem,
              _symbol.queryName() + "_c" + tupleIndex + nameSuffixForMonomial.apply(monomial),
              0, 3))
          .collect(Collectors.toList());

      _coefficientVariables.add(coefficients);

      return argumentTuples -> {
        List<IntegerExpression> parts = new ArrayList<>();
        for (int i = 0; i < monomials.size(); i++) {
          List<IntegerExpression> factors = new ArrayList<>();
          factors.add(coefficients.get(i));
          for (ArgPosition pos : monomials.get(i))
            factors.add(argumentTuples.get(pos.argIndex()).get(pos.argTupleIndex()));

          parts.add(factors.size() == 1 ? factors.get(0) : SmtFactory.createMultiplication(factors));
        }
        return SmtFactory.createAddition(parts).simplify();
      };
    }

    private Function<List<List<IntegerExpression>>, IntegerExpression> buildConstantFunction(int tupleIndex) {
      return buildPolynomialFunction(tupleIndex,
          List.of(List.of()), // a single monomial with no variable factors
          monomial -> "");
    }

    private Function<List<List<IntegerExpression>>, IntegerExpression> buildLinearFunction(int tupleIndex) {
      List<List<ArgPosition>> monomials = allArgumentPositions().stream()
          .map(List::of) // each position alone: c * x_i
          .collect(Collectors.toList());

      return buildPolynomialFunction(tupleIndex, monomials,
          monomial -> positionSuffix(monomial.get(0)));
    }

    private Function<List<List<IntegerExpression>>, IntegerExpression> buildSquaredFunction(int tupleIndex) {
      List<List<ArgPosition>> monomials = allArgumentPositions().stream()
          .map(p -> List.of(p, p)) // each position twice: c * x_i * x_i
          .collect(Collectors.toList());

      return buildPolynomialFunction(tupleIndex, monomials,
          monomial -> positionSuffix(monomial.get(0)) + "_sq");
    }

    private Function<List<List<IntegerExpression>>, IntegerExpression> buildInteractionsFunction(int tupleIndex) {
      List<ArgPosition> positions = allArgumentPositions();
      List<List<ArgPosition>> monomials = new ArrayList<>();

      // For each pair of positions, create a monomial with both positions: c * x_i *
      // x_j
      for (int i = 0; i < positions.size(); i++)
        for (int j = i + 1; j < positions.size(); j++)
          monomials.add(List.of(positions.get(i), positions.get(j)));

      return buildPolynomialFunction(tupleIndex, monomials,
          monomial -> positionSuffix(monomial.get(0)) + positionSuffix(monomial.get(1)));
    }
  }
}
