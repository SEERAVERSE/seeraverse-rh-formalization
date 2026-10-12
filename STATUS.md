# Status

Last updated: 2026-10-12

This document tracks the current formalization status of the
SEERAVERSE Riemann Hypothesis research program.

The project is under active formalization and audit.
A successful Lean build does not by itself imply that every mathematical
or computational obligation has been discharged.

---

## Kernel-checked components

The following major components have been formalized in Lean 4 / Mathlib
and currently build successfully:

- finite Nevanlinna–Pick sufficiency
- Schur reduction and Schur-complement PSD transport
- inverse Schur reconstruction
- Montel / normal-family compactness
- all-depth positivity to a global Schur interpolant
- right-half-plane interpolant construction
- holomorphicity of the right-half-plane interpolant
- positive-real properties of the interpolant
- interpolation at the full Pick lattice
- Jensen / non-Blaschke rigidity
- bounded-holomorphic zero rigidity
- Nevanlinna zero-rigidity reduction
- meromorphic identity continuation
- meromorphicity of `R_boundary` on the right half-plane
- Nevanlinna-class closure under subtraction
- Nevanlinna representation of the interpolant on the far-right half-plane
- pole formation of `R_boundary` from arbitrary-multiplicity zeros of `xi`
- pole-exclusion assembly from the Montel / rigidity data

The theorem

```lean
R_boundary_hasPoleAt_of_xi_zero
```

has been formalized for zeros of arbitrary multiplicity.

The former theorem argument

```text
h_pole_of_zero
```

has been removed from the pole-exclusion and main deduction chain.

---

## Current analytic obligation

The primary remaining analytic obligation is:

```lean
IsNevanlinnaOn R_boundary farRightHalfPlane
```

The current bounded-quotient witness is mathematically explicit:

```text
h(x) = 1 - halfPlaneToDisk(x)
g(x) = h(x) * R_boundary(x)
```

so that

```text
R_boundary(x) = g(x) / h(x).
```

The denominator is holomorphic, bounded, and nonzero on the far-right
half-plane.

The remaining Lean obstruction is the boundedness of `g`.

This has been reduced to a coarse growth estimate for complex digamma,
for example a theorem of the form

```lean
∃ C : ℝ, 0 ≤ C ∧
  ∀ z : ℂ, (9 / 4 : ℝ) ≤ z.re →
    ‖Complex.digamma z‖ ≤ C * (1 + ‖z‖)
```

or an equivalent direct bound sufficient for

```text
(1 - halfPlaneToDisk x) * R_boundary x
```

to be bounded.

Mathlib currently provides functional equations and meromorphicity for
`Complex.digamma`, but not the complex series representation or uniform
growth estimate needed here.

No definition change and no additional analytic axiom have been introduced.

Once this obligation is closed, the already-proved subtraction theorem gives

```lean
IsNevanlinnaOn (fun z => H z - R_boundary z) farRightHalfPlane
```

and the remaining `h_interpolant` assumption can be eliminated from the
rigidity chain.

---

## Remaining analytic integration item

The remaining integration task after the digamma / Nevanlinna step is:

```text
remove h_interpolant
```

by constructing the full `HasMontelRigidityData` object from the already
formalized Montel interpolant and Nevanlinna properties.

The underlying rigidity, identity-continuation, and pole-exclusion theorems
are already present.

---

## Computational certificate

The finite prefix through

```text
1 ≤ N ≤ 4052
```

is currently backed by an external Arb / FLINT clean-room computation.

The Lean interface still contains the project-specific axiom:

```lean
Certificate4052.certificate_freshPivotResidual_positive
```

with direct downstream use in:

```text
freshPivotResidual_positive_of_certificate
freshPivotResidual_positive_prefix
```

This axiom has not been removed.

---

## Clean-room reproduction package

The authoritative clean-room package is:

```text
FINAL_PACKAGE_20261011-013715
```

The original flat execution layout has also been recovered.

The package contains:

- source scripts
- `00_config.json`
- V1 geometry result
- V2 base certificate
- V3 checkpoints
- final V3 state through `N = 4052`
- execution logs
- progress manifests
- environment information
- audit documentation
- SHA256 manifests
- restoration / reproduction tooling

The principal state and configuration files have been checked against the
original flat execution directory and match by SHA256.

The package has been completed without changing the numerical algorithm,
existing numerical results, or checkpoints.

---

## Exact-certificate project

Work is in progress to replace the external certificate axiom with a
kernel-checkable certificate pipeline.

The intended architecture is:

```text
Arb / FLINT computation
        ↓
exact outward-dyadic proof object
        ↓
Arb-free exact-rational replay
        ↓
Lean exact interval / matrix checker
        ↓
Lean theorem
```

The finite arithmetic layer is being separated explicitly from the
analytic-source enclosure layer.

---

## V2 regression status

The export-disabled V2 regression has completed successfully.

Results:

```text
Numerical regression: PASS
V2 computation: completed
Baseline certificate: byte-identical
Exporter: disabled
Proof-object generation: none
```

Baseline certificate SHA256:

```text
ac0dcbbe0592c307b0c45eba6f41a14ef01c3c9426b202eb3c98d1021c1c1f83
```

The process later exited with code `1` only because the Windows CP932 console
could not encode an em dash (`U+2014`) during post-certificate output.

The numerical certificate had already been written and hash-verified before
that stdout encoding exception.

Accordingly:

```text
Numerical / certificate regression: PASS
CLI termination: post-computation encoding failure
```

The issue is treated as an execution-environment output problem, not as a
numerical regression difference.

---

## V2 exact-export status

An export-enabled V2 run is currently in progress.

Environment:

```text
PYTHONIOENCODING=utf-8
SEERAVERSE_EXACT_EXPORT=1
```

The run uses a frozen source snapshot.

Principal source hashes:

```text
kernel.py
d295955ba23342ef48724422ed2d37d0de4b0af7bacc927c89afd13647b194e0

v2_base3203.py
36b4e01038f298ad85f62dc512a23efc26e6032ba1feb334be44bd9fe92e2629

exact_export.py
e3d7c4e94dd9d86c0efe1d08ae80c9674d2be6d4f51cb274e26d17d765b80ac2

00_config.json
0172100ecf378053c2933408749ace85c9f90261ad79c5009c0b2d0048c69887
```

Current run directory:

```text
runs/export_enabled_1
```

The run has not yet been classified as CLOSED.

After completion it must be checked for:

- numerical certificate equality with baseline
- successful exit status
- proof-object generation
- deterministic canonical proof-object hashes
- Arb-free exact-rational replay
- tamper-test failure on corrupted proof operands

---

## Exact finite-arithmetic trust model

The future finite checker must recompute rather than trust:

- interval arithmetic
- Schur denominator safety
- Jacobian bounds
- matrix products
- residual bounds
- row sums
- contraction constants
- box-containment inequalities
- denominator nonzero conditions
- final strict inequalities

The following are diagnostics only and must not determine success:

- PASS flags
- printed decimal bounds
- worst-row indices
- worst-interval summaries
- row counts
- floating-point similarity scales
- cached `e0`
- cached `eI`
- cached `corr`
- cached final ratio

---

## Schur denominator reduction

The V2 denominator audit showed that the large family of Schur recurrence
denominators does not need to be exported entry-by-entry.

The generic invariants

```text
|κ| < 1
|u| < 1
0 < p < 1
```

are sufficient to prove recurrence denominator positivity / nonvanishing.

Therefore the future checker should use generic exact lemmas rather than
millions of stored denominator intervals.

Individual exact sign checks remain necessary for:

```text
r_n + pi1
similarity scale
rho
```

---

## C0 precision bridge

The V2 audit identified three distinct midpoint matrices used at different
precisions:

```text
C0_delta
  constructed inside normalized_interval_data
  effective precision: 9000 dps

C0_residual
  constructed through verify_center_residual / center_block_row
  effective precision: 520 dps

C0_precond
  used during construction of B
  effective precision: 420 dps
```

These matrices must not be silently identified.

For the conservative exact-replay design:

```text
Bridge
  = C0_delta - C0_residual

eI_total
  = eI_semantic + ‖B * Bridge‖∞

final_ratio
  = e0 + eI_total + corr
```

`Bridge` and its norm are to be recomputed exactly from proof data, not trusted
as summaries.

A further audit is evaluating whether a single canonical exact center Jacobian
can be regenerated directly by the checker, which could remove the need to
store the historical midpoint matrices entry-by-entry.

---

## Exact-export design documents

The current certificate work is documented in:

```text
DATAFLOW_MAP.md
EXPORT_SCHEMA.md
EXACT_EXPORT_PATCH.md
DENOMINATOR_REDUCTION.md
V2_PROOF_OBLIGATIONS.md
C0_PRECISION_BRIDGE.md
V2_MINIMAL_PROOF_PAYLOAD.md
```

These documents are design / audit artifacts.

They do not themselves remove the Lean certificate axiom.

---

## Analytic-source trust boundary

Exact export of Arb endpoints does not by itself prove inside Lean that the
corresponding transcendental values lie in those intervals.

The following remain a distinct analytic-source obligation:

- Riemann zeta enclosures
- zeta log-derivative enclosures
- logarithmic source terms
- Euler–Mascheroni constant terms
- other transcendental source evaluations used by the finite certificate

The finite exact checker may initially treat these intervals as explicit
external inputs.

A later analytic-source bridge is required for full kernel trust.

---

## Build status

The current Lean source has been verified in both the local development
environment and GitHub Actions CI.

Local build:

```text
Target:
SEERAVERSE.MainChain

Result:
PASS

Build:
8965 / 8965 jobs completed successfully
```

GitHub Actions CI:

```text
Workflow:
Lean CI

Environment:
GitHub-hosted Ubuntu runner

Result:
PASS

Verified commit:
665e9d5
```

This establishes cross-environment build reproducibility for the current
repository source. It does not by itself discharge the remaining analytic,
certificate, or external-source trust obligations tracked elsewhere in this
document and in `AUDIT.md`.

The principal recently audited theorems reported only standard Lean axioms:

```text
[propext, Classical.choice, Quot.sound]
```

including:

```text
R_boundary_meromorphic_on_rightHalfPlane
halfPlaneInterpolant_isNevanlinnaOn_farRightHalfPlane
R_boundary_hasPoleAt_of_xi_zero
main_riemann_hypothesis_deduction
```

The axiom output of a high-level theorem must not be interpreted in isolation:
remaining theorem hypotheses and external computational dependencies are
tracked separately in `AUDIT.md`.

---

## Primary remaining obligations

The current principal obligations are:

1. close the complex digamma growth estimate needed for
   `IsNevanlinnaOn R_boundary farRightHalfPlane`;

2. remove `h_interpolant` by assembling the already-developed Montel /
   Nevanlinna / rigidity data;

3. complete the V2 exact-export and Arb-free exact-rational replay;

4. extend exact export and replay to V3 through `N = 4052`;

5. implement the Lean exact interval / finite-matrix checker;

6. replace
   `Certificate4052.certificate_freshPivotResidual_positive`
   with a kernel-checked theorem;

7. formalize or otherwise discharge the analytic-source enclosure bridge
   currently supplied by Arb.

---

## Current top-level status

```text
Finite Pick / Schur infrastructure:
KERNEL-CHECKED

Montel / global interpolant:
KERNEL-CHECKED

Jensen / rigidity:
KERNEL-CHECKED

Meromorphic continuation:
KERNEL-CHECKED

xi zero → R_boundary pole:
KERNEL-CHECKED

R_boundary Nevanlinna membership:
OPEN — reduced to digamma growth

Montel-rigidity final integration:
OPEN — h_interpolant removal

Finite prefix certificate:
EXTERNALLY CERTIFIED
Lean kernel replacement in progress

V2 numerical regression:
PASS

V2 exact-export:
RUNNING

V3 exact-export:
NOT STARTED

Lean finite-certificate checker:
NOT YET IMPLEMENTED

Lean source build:
PASS — local, 8965 / 8965 jobs

GitHub Actions CI:
PASS — Lean CI, GitHub-hosted Ubuntu, commit 665e9d5

Full end-to-end kernel verification:
NOT YET COMPLETE
```

---

## Verification policy

This project follows the following audit policy:

- no `sorry` in completed proof blocks
- no new project-specific axioms
- remaining assumptions are kept explicit
- external computational results are not silently promoted to Lean theorems
- successful compilation alone is not treated as mathematical closure
- diagnostic summaries are not proof inputs
- external numerical certificates must be independently replayable
- finite arithmetic and analytic-source trust are audited separately
- high-level theorem axiom reports are interpreted together with theorem
  hypotheses and external dependencies

The objective is not merely to obtain a compiling top-level theorem, but to
make the full dependency chain explicit and progressively move each remaining
trust boundary into machine-checkable form.
