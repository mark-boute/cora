package cora.termination.dependency_pairs;

import cora.rewriting.TRS;
import cora.termination.Handler.Answer;
import cora.termination.Prover;
import cora.termination.dependency_pairs.certification.Informal;
import cora.termination.dependency_pairs.processors.*;
import cora.utils.Pair;
import org.checkerframework.checker.units.qual.K;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Stack;

import static cora.termination.Handler.Answer.*;

public class DPFramework implements Prover {

  @Override
  public Boolean isTRSApplicable(TRS trs) {
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    return checker.checkAccessibility();
  }

  private static Problem computeInitialProblem(TRS trs) {
    return DPGenerator.generateProblemFromTrs(trs);
  }

  @Override
  public Pair< Answer, Optional<String> > proveTermination(TRS trs) {
    if (isTRSApplicable(trs)) {
      GraphProcessor   graphProcessor    = new GraphProcessor();
      SubtermProcessor subtermProcessor = new SubtermProcessor();
      KasperProcessor  kasperProcessor  = new KasperProcessor();
      TheoryArgumentsProcessor targProcessor = new TheoryArgumentsProcessor();
      SplittingProcessor splitProcessor = new SplittingProcessor();

      Informal.getInstance().addProofStep("We start by calculating the following Static Dependency Pairs:");

      Problem initialProblem = DPFramework.computeInitialProblem(trs);

      // we start with the processors that preserve the "public" nature of a chain
      initialProblem = splitProcessor.transform(initialProblem);
      initialProblem = targProcessor.transform(initialProblem);

      // First, we compute the graph of the initial problem.
      Optional<List<Problem>> dppsFromGraph = graphProcessor.processDPP(initialProblem);

      if (dppsFromGraph.isEmpty()) {
        return new Pair<>(MAYBE, Optional.empty());
      } else {
        List<Problem> toBeSolved = dppsFromGraph.get();

        // Trying to solve each problem in toBeSolved
        while (!toBeSolved.isEmpty()) {
          // Get the first problem in the list of problems to be solved
          Problem p = toBeSolved.getFirst();
          // Try subterm processor
          Optional<List<Problem>> subterm = subtermProcessor.processDPP(p);
          if (subterm.isPresent()) {
            toBeSolved.removeFirst();
            toBeSolved.addAll(subterm.get());
          } else {
            // Try kasper's processor
            Optional<List<Problem>> kasper = kasperProcessor.processDPP(p);
            if (kasper.isPresent()) {
              toBeSolved.removeFirst();
              toBeSolved.addAll(kasper.get());
            } else {
              // Here the problem failed in all processors and couldn't be solved
              return new Pair<>(MAYBE, Optional.empty());
            }
          }
        }
        return new Pair<>(YES, Optional.of(Informal.getInstance().getInformalProof()));
      }
    } else {
      return new Pair<>(MAYBE, Optional.empty());
    }
  }
}
