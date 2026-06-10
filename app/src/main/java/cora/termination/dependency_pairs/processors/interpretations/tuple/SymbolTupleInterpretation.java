package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

import charlie.smt.IVar;
import charlie.smt.IntegerExpression;
import charlie.smt.SmtFactory;
import charlie.smt.SmtProblem;

import charlie.terms.FunctionSymbol;

public class SymbolTupleInterpretation {

  // private final List<IntegerExpression> _tupleExpressions;
  private final List<Function<List<List<IntegerExpression>>, IntegerExpression>> _polynomialFunctions;

  private final List<List<IVar>> _argumentVariables;
  private final TupleConfiguration _config;
  private final FunctionSymbol _symbol;

  private SymbolTupleInterpretation(
    List<Function<List<List<IntegerExpression>>, IntegerExpression>> polynomialFunctions, 
    List<List<IVar>> argumentVariables,
    TupleConfiguration config,
    FunctionSymbol symbol
  ) {

    _polynomialFunctions = polynomialFunctions;
    _argumentVariables = argumentVariables;
    _config = config;
    _symbol = symbol;
  }

  public List<IntegerExpression> apply(List<List<IntegerExpression>> argumentTuples) {
    return _polynomialFunctions.stream()
        .map(f -> f.apply(argumentTuples))
        .collect(Collectors.toList());
  }

  public List<IntegerExpression> getTuple() {
    // _argumentVariables is [tupleIndex][argIndex], apply wants
    // [argIndex][tupleIndex]
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

  public TupleConfiguration getConfig() {
    return _config;
  }

  public static class Builder {
    private final SmtProblem _problem;
    private final FunctionSymbol _symbol;
    private final TupleConfiguration _config;
    private final List<List<IVar>> _argumentVariables;

    public Builder(SmtProblem problem, FunctionSymbol symbol, TupleConfiguration config) {
      if (config.size() < 1)
        throw new IllegalArgumentException("Tuple length must be at least 1");

      _problem = problem;
      _symbol = symbol;
      _config = config;
      _argumentVariables = createArgumentVariables();
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
          System.out.println("Partial application for interactions not implemented yet: " + buildInteractions(tupleIndex + 1));
          // function.add(buildInteractionsFunction(tupleIndex + 1));

        functions.add(args -> SmtFactory.createAddition(
            function.stream().map(f -> f.apply(args)).collect(Collectors.toList())).simplify());
      }

      return new SymbolTupleInterpretation(functions, _argumentVariables, _config, _symbol);
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

    private Function<List<List<IntegerExpression>>, IntegerExpression> buildConstantFunction(int tupleIndex) {
      // Created once, lives in the closure, registered with _problem
      IVar constant = SmtFactory.createIntegerVariable(
          _problem, _symbol.queryName() + "_c" + tupleIndex, 0, 10);
      return args -> constant;
    }

    private Function<List<List<IntegerExpression>>, IntegerExpression> buildLinearFunction(int tupleIndex) {
      // All coefficient IVars created here, captured by the lambda
      List<List<IVar>> coefficients = new ArrayList<>();
      for (int argIndex = 0; argIndex < _symbol.queryArity(); argIndex++) {
        List<IVar> row = new ArrayList<>();
        for (int argTupleIndex = 0; argTupleIndex < _config.size(); argTupleIndex++) {
          row.add(SmtFactory.createIntegerVariable(_problem,
              _symbol.queryName() + "_c" + tupleIndex
                  + "_x" + (argIndex + 1) + "_" + (argTupleIndex + 1),
              0, 10));
        }
        coefficients.add(row);
      }

      return argumentTuples -> {
        List<IntegerExpression> parts = new ArrayList<>();
        for (int argIndex = 0; argIndex < _symbol.queryArity(); argIndex++)
          for (int argTupleIndex = 0; argTupleIndex < _config.size(); argTupleIndex++)
            parts.add(SmtFactory.createMultiplication(
                coefficients.get(argIndex).get(argTupleIndex),
                argumentTuples.get(argIndex).get(argTupleIndex)));
        return SmtFactory.createAddition(parts).simplify();
      };
    }

    private Function<List<List<IntegerExpression>>, IntegerExpression> buildSquaredFunction(int tupleIndex) {
      // All coefficient IVars created here, captured by the lambda
      List<List<IVar>> coefficients = new ArrayList<>();
      for (int argIndex = 0; argIndex < _symbol.queryArity(); argIndex++) {
        List<IVar> row = new ArrayList<>();
        for (int argTupleIndex = 0; argTupleIndex < _config.size(); argTupleIndex++) {
          row.add(SmtFactory.createIntegerVariable(_problem,
              _symbol.queryName() + "_c" + tupleIndex
                  + "_x" + (argIndex + 1) + "_" + (argTupleIndex + 1) + "_sq",
              0, 10));
        }
        coefficients.add(row);
      }

      return argumentTuples -> {
        List<IntegerExpression> parts = new ArrayList<>();
        for (int argIndex = 0; argIndex < _symbol.queryArity(); argIndex++) {
          for (int argTupleIndex = 0; argTupleIndex < _config.size(); argTupleIndex++) {
            IntegerExpression x = argumentTuples.get(argIndex).get(argTupleIndex);
            parts.add(SmtFactory.createMultiplication(
                coefficients.get(argIndex).get(argTupleIndex),
                SmtFactory.createMultiplication(x, x)));
          }
        }
        return SmtFactory.createAddition(parts).simplify();
      };
    }

    // Interaction terms: c * xi_a * xj_b where (i,a) <_lex (j,b)
    private IntegerExpression buildInteractions(int tupleIndex) {
      List<IntegerExpression> parts = new ArrayList<>();
      for (int argIndex1 = 0; argIndex1 < _symbol.queryArity(); argIndex1++) {
        for (int argTupleIndex1 = 0; argTupleIndex1 < _config.size(); argTupleIndex1++) {
          for (int argIndex2 = argIndex1; argIndex2 < _symbol.queryArity(); argIndex2++) {
            // When same argument, start strictly above argTupleIndex1 to avoid
            // both the diagonal (xi_j * xi_j) and duplicate (xi_j * xi_k) and (xi_k * xi_j)
            int startTupleIndex2 = (argIndex2 == argIndex1) ? argTupleIndex1 + 1 : 0;
            for (int argTupleIndex2 = startTupleIndex2; argTupleIndex2 < _config.size(); argTupleIndex2++) {
              IVar coeff = SmtFactory.createIntegerVariable(
                  _problem,
                  _symbol.queryName() + "_c" + tupleIndex
                      + "_x" + (argIndex1 + 1) + "_" + (argTupleIndex1 + 1)
                      + "_x" + (argIndex2 + 1) + "_" + (argTupleIndex2 + 1),
                  0, 10);
              parts.add(SmtFactory.createMultiplication(coeff,
                  SmtFactory.createMultiplication(
                      _argumentVariables.get(argTupleIndex1).get(argIndex1),
                      _argumentVariables.get(argTupleIndex2).get(argIndex2))));
            }
          }
        }
      }
      return SmtFactory.createAddition(parts).simplify();
    }
  }

}

/*
 * Here we generate the tuple for linear interpretations.
 * For example, for tuple length k, and number of arguments n, we may construct:
 * 
 * [[ a(x1, x2, ... xn) ]] = (
 * a_c1 + sum_{i=1}^k (a_c1_x1_i * x1_i) + ... + sum_{i=1}^k (a_c1_xn_i * xn_i),
 * a_c2 + sum_{i=1}^k (a_c2_x1_i * x1_i) + ... + sum_{i=1}^k (a_c2_xn_i * xn_i),
 * ...
 * a_ck + sum_{i=1}^k (a_ck_x1_i * x1_i) + ... + sum_{i=1}^k (a_ck_xn_i * xn_i)
 * )
 * 
 * Here the contants should be read as follows:
 * - a is the symbol being interpreted
 * - a_cj is the constant term for the j-th element of the tuple
 * - a_cj_xm_i is the coefficient for
 * the j-th element of the tuple,
 * for the m-th argument,
 * and the i-th element of the tuple that belongs to the m-th argument.
 * - xn_i is the i-th element of the tuple that belongs to the n-th argument.
 */
