## The decomposer is correct — the configuration is the bug

`combineTermsOnParameterVariables` is doing exactly what it should. The `-1 >= 0` accurately reflects that **the polynomial `c · x² − x` cannot be proven non-negative by treating the two monomials independently**. This is a fundamental limit of absolute positiveness: it only works when every monomial coefficient is non-negative on its own.

The problem is in the configuration. Element 2 has `CONSTANT + SQUARED` but no `LINEAR`. So the left side has `c·x₂²` but nothing to absorb the `−x₂` that comes from the right side.

### The coupling that must be captured

`c · x₂² − x₂ ≥ 0` for all non-negative integers requires `c ≥ 1` (check at x₂ = 1: `c − 1 ≥ 0`). You cannot prove this independently for the two monomials — the terms are coupled.

### Fix A: configuration (recommended)

Add `LINEAR` to any tuple element that will receive a linear contribution from the right-hand side (which is essentially all of them):

```java
TupleConfig config = TupleConfig.of(
    ElementConfig.of(Part.CONSTANT, Part.LINEAR),
    ElementConfig.of(Part.CONSTANT, Part.LINEAR, Part.SQUARED)  // LINEAR required here
);
```

With `LINEAR` present, element 2 gains a `c_lin · x₂` term on the left side. The decomposer then sees the coefficient of `_x_2` as `c_lin − 1` (accumulated via `addCoefficient`), and emits the satisfiable constraint `c_lin ≥ 1` instead of the constant `-1 ≥ 0`.

---

### Fix B: smarter decomposition (if you want SQUARED-only configs to stay valid)

After collecting the per-monomial map, do a second pass that detects the coupling and replaces the two independent constraints with one joint one:

```java
private void emitConstraints(
        Map<IntegerExpression, IntegerExpression> coeffMap,
        List<IVar> paramVars,
        SmtProblem problem) {

    for (Map.Entry<IntegerExpression, IntegerExpression> entry : coeffMap.entrySet()) {
        IntegerExpression monomial = entry.getKey();
        IntegerExpression coeff    = entry.getValue();

        if (isNegativeConstant(coeff)) {
            // e.g. coefficient of _x_2 is -1
            // check if _x_2 * _x_2 exists in the map with a positive SMT coefficient
            IntegerExpression squared = findSquaredKey(monomial, coeffMap, paramVars);
            if (squared != null) {
                // Replace:  c_sq >= 0  AND  -k >= 0
                // With:     c_sq >= k            (the correct coupled constraint)
                long k = -constantValue(coeff);
                problem.require(SmtFactory.createGeq(
                    SmtFactory.createAddition(
                        coeffMap.get(squared),
                        SmtFactory.createValue(-k)  // c_sq - k >= 0
                    ).simplify()
                ));
                // skip both individual entries — they're consumed here
                continue;
            }
            // No squared counterpart: truly unsat, let -k >= 0 fire as before
        }

        problem.require(SmtFactory.createGeq(coeff));
    }
}
```

Fix A is cleaner and keeps the proof logic simple. Fix B is useful if you need configurations where SQUARED appears without LINEAR for efficiency reasons, and you want the solver to still find valid coefficients. For now I'd go with Fix A and only reach for Fix B if you have a concrete reason to exclude LINEAR from some element.

## My answer

I do not yet know what my config may look like, it is part of my experiment.

Quick note however: any term's interpretation is always at least 0, so no value in a variable tuple can be negative. Neither can the coefficients.

## Claude

## The domain property that makes this work

For any x ∈ ℕ: **x² ≥ x**, because x² − x = x(x−1) ≥ 0 for all natural numbers. This is the property your non-negativity note unlocks.

So instead of treating `c·x²` and `−x` as independent constraints, you can **promote** the negative linear entry into the squared entry:

```
c·x² − x ≥ 0  for all x ∈ ℕ
  iff  (c−1)·x² + c·x²(x−1) ≥ 0  [x(x−1) ≥ 0 absorbed]
  iff  c ≥ 1  [sufficient: check at x=1]
```

The general promotion rule: if monomial key `m` has a negative integer component, and `m·xi` (where xi already appears in `m`) is another key in the map, then **merge** them using `m·xi ≥ m`:

```java
private void emitConstraints(
        Map<IntegerExpression, IntegerExpression> coeffMap,
        SmtProblem problem) {

    // Promotion pass: absorb negative-constant entries into their
    // squared counterpart (valid because xi^2 >= xi for xi in NN)
    Map<IntegerExpression, IntegerExpression> promoted = new HashMap<>(coeffMap);

    for (Map.Entry<IntegerExpression, IntegerExpression> entry : coeffMap.entrySet()) {
        IntegerExpression coeff = entry.getValue();
        long negPart = extractNegativeConstant(coeff); // returns 0 if none

        if (negPart < 0) {
            IntegerExpression monomial = entry.getKey();
            IntegerExpression squared = findSquaredKey(monomial, promoted);
            // xi^2 >= xi, so we can require coeff(xi^2) + negPart >= 0
            // instead of negPart >= 0
            if (squared != null) {
                promoted.merge(squared,
                    SmtFactory.createValue((int) -negPart),
                    (existing, added) -> SmtFactory.createAddition(existing, 
                                             SmtFactory.createNegation(added)).simplify());
                promoted.remove(monomial);
            }
        }
    }

    promoted.values().stream()
        .map(SmtFactory::createGeq)
        .forEach(problem::require);
}
```

`findSquaredKey` looks for an entry whose monomial is `m·xi` for any `xi` that already appears in `m`. For the linear case (`m = _x_2`), it looks for `_x_2 · _x_2`, which is exactly the squared key in your map.

The promotion is **only valid when xi already appears in m**. You cannot promote `_x_2` into `_x_1·_x_2` (an interaction term), because `_x_1·_x_2 ≥ _x_2` requires `_x_1 ≥ 1`, which is not guaranteed. Only same-variable squaring is unconditionally safe over ℕ.
