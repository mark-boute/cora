package cora.termination.dependency_pairs.processors.interpretations.tuple;

import java.util.List;

public record TupleConfiguration(List<PolynomialConfiguration> elements) {

  public TupleConfiguration {
    if (elements.isEmpty())
      throw new IllegalArgumentException("Tuple must have at least one element");
    elements = List.copyOf(elements);
  }

  public static TupleConfiguration of(PolynomialConfiguration... elements) {
    return new TupleConfiguration(List.of(elements));
  }

  public int size() {
    return elements.size();
  }

  public PolynomialConfiguration get(int i) {
    return elements.get(i);
  }
}