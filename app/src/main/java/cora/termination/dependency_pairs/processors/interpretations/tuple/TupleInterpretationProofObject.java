package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import charlie.terms.FunctionSymbol;
import charlie.trs.Rule;
import charlie.util.Pair;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

public class TupleInterpretationProofObject extends ProcessorProofObject {

  private String _reason;
  private Boolean _success = false;

  Set<DP> _orientedDPs;
  Map<FunctionSymbol, List<String>> _symbolInterpretations;
  Map<Rule, Pair<List<String>, List<String>>> _ruleInterpretations;
  Map<DP, Pair<List<String>, List<String>>> _DPInterpretations;

  /**
   * A failed proof; SMT-Solver returned NO.
   * 
   * @param input
   */
  protected TupleInterpretationProofObject(Problem input) {
    super(input);
  }

  /**
   * A MAYBE proof; SMT-Solver did not find a configuration to match the
   * constraints.
   * 
   * @param input
   * @param reason The reason returned by the SMT-Solver
   */
  public TupleInterpretationProofObject(Problem input, String reason) {
    super(input);
    _reason = reason;
  }

  public TupleInterpretationProofObject(
      Problem input,
      Set<DP> orientedDPs,
      Map<FunctionSymbol, List<String>> symbolInterpretations,
      Map<Rule, Pair<List<String>, List<String>>> ruleInterpretations,
      Map<DP, Pair<List<String>, List<String>>> dpInterpretations) {
    super(input, input.removeDPsByValue(orientedDPs, false));
    _success = orientedDPs != null && !orientedDPs.isEmpty();

    _orientedDPs = orientedDPs;
    _symbolInterpretations = symbolInterpretations;
    _ruleInterpretations = ruleInterpretations;
    _DPInterpretations = dpInterpretations;
  }

  @Override
  public void justify(OutputModule module) {
    if (!_success) {
      if (_reason != null) {
        module.println("The SMT-Solver returned MAYBE with reason: " + _reason);
      } else {
        module.println("The SMT-Solver returned NO, no tuple interpretation exists.");
      }
      return;
    }

    module.println("A suitable tuple interpretation was found.");
    module.println("Interpretation tuples for function symbols:");

    this.printSymbolInterpretations(module);

    module.println("This yields the following interpretations for the rules:");

    this.printRuleInterpretations(module);

    // only print if there are some non-oriented DPs
    boolean hasNonOrientedDPs = _orientedDPs.size() != _input.getDPList().size();

    if (hasNonOrientedDPs) {
      module.println("The following interpretations for the non-oriented dependency pairs:");
      this.printDPInterpretations(module, false);
    }

    module.println("And the following interpretations for the oriented dependency pairs:");
    this.printDPInterpretations(module, true);

    if (hasNonOrientedDPs)
      module.println("Done with run, next run:");
  }

  @Override
  public String queryProcessorName() {
    return "Tuple Interpretation Processor";
  }

  private void printSymbolInterpretations(OutputModule module) {
    _symbolInterpretations.forEach((symbol, interpretation) -> {

      String variables = IntStream.rangeClosed(1, symbol.queryArity())
          .mapToObj(i -> "x" + i)
          .collect(Collectors.joining(", ", "(", ")"));

      module.print("J(%a)" + variables, symbol);
      module.print(" = ");
      this.printTuple(module, interpretation);
    });
  }

  private void printRuleInterpretations(OutputModule module) {
    _ruleInterpretations.forEach((rule, interpretation) -> {
      module.println("%a is interpreted as [[%a]] >= [[%a]], or: ", rule, rule.queryLeftSide(), rule.queryRightSide());
      this.printTuple(module, interpretation.left());
      module.print(">= ");
      this.printTuple(module, interpretation.right());
    });
  }

  private void printDPInterpretations(OutputModule module, boolean oriented) {
    _DPInterpretations.entrySet().stream()
        .filter(entry -> oriented == _orientedDPs.contains(entry.getKey()))
        .forEach(entry -> {
          DP dp = entry.getKey();
          Pair<List<String>, List<String>> interpretation = entry.getValue();

          String comparison = oriented ? ">" : ">=";

          module.println("%a → %a is interpreted as [[%a]] %a [[%a]], or: ",
              dp.rhs(), dp.lhs(), dp.lhs(), comparison, dp.rhs());

          this.printTuple(module, interpretation.left());
          module.print(comparison + " ");
          this.printTuple(module, interpretation.right());
        });

  }

  private void printTuple(OutputModule module, List<String> tuple) {
    // if sum of length of string < 80, print in one line. Otherwise, print in
    // multiple lines.
    String tupleString = tuple.stream().collect(Collectors.joining(", ", "❬", "❭"));
    if (tupleString.length() < 80) {
      module.println(tupleString);
    } else {
      module.println(tuple.stream().collect(Collectors.joining(",\n\t", "❬\n\t", "\n❭")));
    }
  }

}
