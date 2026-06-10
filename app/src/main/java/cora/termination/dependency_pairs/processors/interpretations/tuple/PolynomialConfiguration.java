package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.Collections;
import java.util.EnumSet;
import java.util.Set;

enum PolynomialPart {
  CONSTANT, LINEAR, SQUARED, INTERACTIONS
}

public record PolynomialConfiguration(Set<PolynomialPart> parts) {

  public PolynomialConfiguration {
    parts = parts.isEmpty()
        ? Collections.emptySet()
        : Collections.unmodifiableSet(EnumSet.copyOf(parts));
  }

  public static PolynomialConfiguration of(PolynomialPart first, PolynomialPart... rest) {
    return new PolynomialConfiguration(EnumSet.of(first, rest));
  }

  public boolean has(PolynomialPart part) {
    return parts.contains(part);
  }
}