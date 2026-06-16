package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
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
    System.out.println("No tuple interpretation exists for this problem.");
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
    System.out.println("The SMT-Solver returned MAYBE with reason: " + reason);
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
      printComparison(module, interpretation.left(), interpretation.right(), ">=");
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
          printComparison(module, interpretation.left(), interpretation.right(), comparison);
        });
  }

  private static final Pattern REPEATED_FACTOR = Pattern.compile("(\\w+)( \\* \\1)+");

  private static final Pattern VAR_NAME = Pattern.compile("\\w+_\\w+");

  private String pretty(String s) {
    s = s.replaceAll("\\[([^\\]]+)\\]", "$1");  // strip IVar brackets: [x1_1] → x1_1
    // Collapse x * x * ... * x → [x^n]  (one pass, any degree)
    Matcher m = REPEATED_FACTOR.matcher(s);
    StringBuffer sb = new StringBuffer();
    while (m.find()) {
      String var = m.group(1);
      int count = 1 + (m.group(0).length() - var.length()) / (" * " + var).length();
      String power = count == 1 ? var : var + "^" + count;
      m.appendReplacement(sb, Matcher.quoteReplacement("[" + power + "]"));
    }
    m.appendTail(sb);
    final String collapsed = sb.toString();
    // Re-bracket bare variable names (contain underscore, were not part of a repeated group)
    return VAR_NAME.matcher(collapsed).replaceAll(r -> {
      int start = r.start();
      if (start > 0 && collapsed.charAt(start - 1) == '[') return r.group();
      return "[" + r.group() + "]";
    });
  }

  private String tupleInline(List<String> tuple) {
    return tuple.stream().map(this::pretty).collect(Collectors.joining(", ", "❬", "❭"));
  }

  private void printComparison(OutputModule module, List<String> left, List<String> right, String op) {
    String leftStr = tupleInline(left);
    String rightStr = tupleInline(right);
    if ((leftStr + " " + op + " " + rightStr).length() < 80) {
      module.println(leftStr + " " + op + " " + rightStr);
    } else {
      printTuple(module, left, leftStr);
      module.print(op + " ");
      printTuple(module, right, rightStr);
    }
  }

  private void printTuple(OutputModule module, List<String> tuple) {
    printTuple(module, tuple, tupleInline(tuple));
  }

  private void printTuple(OutputModule module, List<String> tuple, String inline) {
    if (inline.length() < 80) {
      module.println(inline);
    } else {
      module.println(tuple.stream().map(this::pretty)
          .collect(Collectors.joining(",\n\t", "❬\n\t", "\n❭")));
    }
  }

}
