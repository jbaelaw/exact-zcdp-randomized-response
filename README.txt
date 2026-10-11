Exact zCDP for k-Ary Randomized Response — Lean formalization
Ji Ho Bae / LawAll AI / jihobae@snu.ac.kr
Companion to https://doi.org/10.5281/zenodo.23288478

This project formalizes the complete main characterization and the exact-real-
arithmetic bisection corollary of the published English manuscript. The domain
is every natural k >= 2 and every real privacy parameter epsilon >= 0.

Reproduction
------------
Lean: leanprover/lean4:v4.34.1
mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612
All transitive dependencies are pinned in lake-manifest.json.

With elan installed, run from this directory:
  lake exe cache get
  lake --wfail build
  lake env lean verification/Audit.lean

The first command obtains compiled mathlib dependencies at the pinned revision.
The second builds every project module and fails on project build warnings.
The third prints the complete axiom closure for every public theorem and lemma.
The source project is platform independent; no local .lake artifacts are shipped.
The task-specific verification/full_build.sh also rebuilds this project's modules
in dependency order to bound compiler memory on the designated Linux host.

Scope and principal results
---------------------------
Import ExactZCDP. All declarations are in namespace ExactZCDP.

Mechanism.lean defines the actual probabilities on Fin k, proves positivity and
normalization, defines Renyi divergence as the logarithm of its finite real-power
sum, and evaluates that sum. Fin k is a zero-based relabeling of the paper's [k].
IsZCDP quantifies over all ordered input pairs and all real orders alpha > 1.
It includes nonnegativity of the proposed privacy parameter.

Main.lean:
  isZCDP_iff_exact — exact all-order equivalence for every k >= 2, epsilon >= 0.
  exactParameter_isLeast — the least element of the set of valid parameters.
  exactParameter_zero — the uniform-mechanism boundary case.
  endpoint_formula_iff — exact threshold equivalence, including equality.
  endpoint_profile_strictAnti — strict decrease in the endpoint regime.
  interior_unique_root — uniqueness in x > epsilon/2 of the printed equation.
  interior_characterization — root, explicit finite bracket, exact value,
      admissible maximizing order, attainment, and uniqueness of that order.
  endpoint_lt_exactParameter — strict improvement above the threshold.

EndpointLimit.lean:
  endpoint_profile_limit — the right-hand limit as alpha tends to 1.

Parameters.lean proves the positivity of the threshold denominator and the exact
algebraic change of variables; the threshold is the expression printed in the paper.
Calculus.lean, ShapeBounds.lean and Shape.lean prove the derivative, persistence,
limit and global uniqueness arguments, without assuming the desired conclusion.
RootEquation.lean connects the auxiliary zero to the printed logarithmic equation.

Bisection.lean formalizes the midpoint algorithm with exact sign comparisons.
Before an exact hit, root and order brackets have the stated exact widths.
After an exact hit, both endpoints remain at the root. It proves value enclosures,
geometric errors, convergence, and the natural-ceiling logarithmic iteration bound.
bisection_corollary uses only the original k/epsilon/threshold hypotheses.

Certificates.lean:
  exact_bisection_certificate — the bounds enclose exactParameter itself.
  exact_bisection_converges — both bounds converge to exactParameter.
  exact_bisection_iteration_bound — a certificate of any prescribed positive width.

Verification boundaries
-----------------------
This is a mathematical formalization over Lean's real numbers. Real exponential,
logarithm and exact comparisons are noncomputable definitions. The iteration
count is an exact-real-arithmetic bound, as in the manuscript; the project does
not claim an executable floating-point implementation or a bit-complexity bound.

There are no sorry/admit placeholders or new axiom declarations in the project.
The final build, dependency audit and file hashes are recorded under verification/.
The paper's literature-priority and bibliographic claims are outside Lean's scope.

Final validation (2026-10-11 KST)
-------------------------------
All project build outputs were removed before the final build on the designated
DigitalOcean Linux host. The clean project build passed with --wfail: no warnings
or errors. The already compiled dependencies were reused at their pinned, clean
Git revisions. All 114 public theorems and lemmas passed an axiom-closure audit;
the only axioms in their combined dependency closure are propext, Classical.choice,
and Quot.sound. No additional axioms or proof placeholders occur. Local source
hashes match the sources of the verified remote build.
