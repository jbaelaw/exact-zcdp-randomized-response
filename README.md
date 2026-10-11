# Exact zCDP for k-Ary Randomized Response

**Ji Ho Bae · LawAll AI · jihobae@snu.ac.kr**

Lean 4 formalization of the complete exact zCDP characterization for k-ary randomized response, for every integer `k ≥ 2` and every real privacy parameter `ε ≥ 0`.

[Paper and DOI](https://doi.org/10.5281/zenodo.23288478) · [English PDF](paper/Exact_zCDP_for_k_ary_Randomized_Response.pdf) · [Verification report](verification/report.json)

## Results

The formalization starts with the actual finite output probabilities and Rényi-divergence sum. It proves the least valid zCDP parameter, the exact endpoint threshold including equality, the unique interior optimizer with an explicit finite bracket, and the complete bisection corollary in exact real arithmetic.

Principal declarations in namespace `ExactZCDP`:

- `isZCDP_iff_exact` and `exactParameter_isLeast`: the full least-parameter characterization.
- `endpoint_formula_iff` and `endpoint_profile_limit`: the threshold and endpoint limit.
- `interior_characterization`: the unique root and maximizing order, exact value, and finite bracket.
- `exact_bisection_certificate`, `exact_bisection_converges`, and `exact_bisection_iteration_bound`: certified value enclosures, convergence, and the prescribed-width iteration bound.

The [module guide](README.txt) describes the remaining declarations. Import `ExactZCDP` to use the full project.

## Reproduce

The project pins Lean **4.34.1**, mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, and all transitive dependencies.

With elan installed, run from the repository root:

```sh
lake exe cache get
lake --wfail build
lake env lean verification/Audit.lean
```

The final build on 11 October 2026 removed all project build outputs before rebuilding and reused clean dependencies at their pinned commits. It passed with **zero warnings and zero errors**. The [axiom audit](verification/axioms.log) covers all **114 public theorems and lemmas**; their combined closure contains only `propext`, `Classical.choice`, and `Quot.sound`. The project contains no `sorry`, `admit`, or added axiom declarations.

The definitions use real exponential, logarithm, and exact sign comparisons. The bisection bound concerns exact real arithmetic, as in the paper; this is not a floating-point implementation or a bit-complexity claim.

## Files and provenance

- `ExactZCDP/`: the proof modules.
- `paper/`: the unchanged published English PDF and its LaTeX source.
- `verification/`: build log, axiom audit, environment, and verification report.
- `SHA256SUMS`: hashes of all distributed repository files other than the manifest itself.

The public environment record omits the compute host address and working directory. The build and axiom logs are preserved unchanged. The 18 proof, configuration, and audit source files retain the exact hashes of the verified build. The original local verification package is preserved separately.

The English paper's AI-use disclosure and author-responsibility statement remain in the manuscript. Literature priority and bibliographic claims are outside the Lean verification scope.
