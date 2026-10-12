# Audit

Last updated: 2026-10-12

This document records the current verification policy, trust boundaries,
axiom status, build status, and computational-certificate audit for the
SEERAVERSE Riemann Hypothesis formalization.

The project is under active formalization and audit.

A successful build, a successful external numerical run, and a high-level
`#print axioms` result are treated as distinct kinds of evidence and are not
interchangeable.

---

## 1. Verification policy

The project currently follows these rules:

- no `sorry` in completed proof blocks
- no new project-specific axioms
- remaining assumptions are kept explicit
- external computational results are not silently promoted to Lean theorems
- successful compilation alone is not treated as mathematical closure
- diagnostic summaries are not proof inputs
- external numerical certificates must be independently replayable
- finite exact arithmetic and analytic-source trust are audited separately
- high-level theorem axiom reports are interpreted together with theorem
  hypotheses and external dependencies
- historical numerical summaries are provenance, not kernel proof objects
- changes to numerical-certificate tooling must preserve the frozen baseline
  unless explicitly re-certified

The objective is not merely to obtain a compiling top-level theorem, but to
make the dependency chain explicit and progressively move each remaining trust
boundary into machine-checkable form.

---

## 2. Build audit

Latest reported local build:

```text
lake build SEERAVERSE.MainChain
Build completed successfully (8965 jobs).
```

The current GitHub repository has not yet independently reproduced this build
through CI.

Until CI is configured and passes on the repository commit, the above result
should be read as a local build report.

---

## 3. Lean axiom audit

The following recently audited theorems were reported to depend only on:

```text
[propext, Classical.choice, Quot.sound]
```

Relevant examples include:

```text
R_boundary_meromorphic_on_rightHalfPlane
halfPlaneInterpolant_isNevanlinnaOn_farRightHalfPlane
R_boundary_hasPoleAt_of_xi_zero
main_riemann_hypothesis_deduction
```

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

### Important interpretation rule

A high-level theorem reporting only standard Lean axioms does not by itself
show that every mathematical or computational responsibility in the overall
research program has been discharged.

The audit therefore separately tracks:

- theorem hypotheses
- upstream formalized components
- external computational certificates
- analytic-source interval obligations
- project-specific axioms

---

## 4. Remaining project-specific axiom

The finite-prefix certificate still depends on:

```lean
Certificate4052.certificate_freshPivotResidual_positive
```

Direct downstream users include:

```text
freshPivotResidual_positive_of_certificate
freshPivotResidual_positive_prefix
```

This axiom has not been removed.

The current Lean source therefore does not yet provide a fully kernel-checked
replacement for the finite computational certificate through `N = 4052`.

---

## 5. Current analytic obligation

The primary remaining analytic obligation is:

```lean
IsNevanlinnaOn R_boundary farRightHalfPlane
```

The current explicit bounded-quotient witness is:

```text
h(x) = 1 - halfPlaneToDisk(x)
g(x) = h(x) * R_boundary(x)
```

with

```text
R_boundary(x) = g(x) / h(x).
```

The denominator side is no longer the obstruction.

The remaining formal obstruction is boundedness of `g`, reduced to a coarse
uniform growth estimate for complex digamma on a right half-plane.

A representative sufficient target is:

```lean
∃ C : ℝ, 0 ≤ C ∧
  ∀ z : ℂ, (9 / 4 : ℝ) ≤ z.re →
    ‖Complex.digamma z‖ ≤ C * (1 + ‖z‖)
```

Mathlib currently provides functional equations and meromorphicity for
`Complex.digamma`, but not the complex series representation or uniform
growth estimate needed here.

No new analytic axiom has been introduced for this step.

Once this obligation is closed, the already-proved subtraction closure gives:

```lean
IsNevanlinnaOn (fun z => H z - R_boundary z) farRightHalfPlane
```

and the remaining `h_interpolant` integration assumption can be eliminated by
assembling the full Montel / Nevanlinna / rigidity data.

---

## 6. Clean-room computational certificate

The authoritative clean-room package is:

```text
FINAL_PACKAGE_20261011-013715
```

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

The original flat execution layout has also been recovered.

Key files from the package have been compared with the original flat working
directory and verified by SHA256.

The package completion work did not change:

- the numerical algorithm
- the existing numerical results
- the checkpoints

---

## 7. V2 numerical-regression audit

The export-disabled V2 regression completed the numerical computation and
produced a certificate byte-identical to the baseline.

Result:

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

The certificate had already been written and hash-verified before that
stdout-encoding exception.

Audit classification:

```text
Numerical / certificate regression: PASS
CLI termination: post-computation stdout encoding failure
```

The encoding issue is treated as an execution-environment output failure, not
as a numerical-regression difference.

---

## 8. V2 exact-export run

An export-enabled V2 run is currently in progress.

Execution environment:

```text
PYTHONIOENCODING=utf-8
SEERAVERSE_EXACT_EXPORT=1
```

Frozen principal source hashes:

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

Run directory:

```text
runs/export_enabled_1
```

The export-enabled run is not yet classified as closed.

Required post-run checks:

- numerical certificate remains identical to the baseline
- process exits successfully
- exact proof-object is generated
- canonical proof-object hashes are recorded
- Arb-free exact-rational replay succeeds
- deterministic re-export is confirmed
- tampering with proof operands causes replay failure

---

## 9. Exact-certificate architecture

The current target architecture is:

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

The certificate design deliberately separates finite arithmetic from analytic
source evaluation.

---

## 10. Finite exact-arithmetic trust layer

The future exact replay and Lean checker must recompute rather than trust:

- rational / dyadic interval arithmetic
- Schur denominator safety
- matrix products
- Jacobian deviation bounds
- residual bounds
- row sums
- contraction constants
- box-containment inequalities
- denominator nonzero conditions
- final strict inequalities

The following are diagnostic only and must not determine acceptance:

- PASS flags
- printed decimal bounds
- worst-row indices
- worst-interval summaries
- row counts
- floating-point scale summaries
- cached `e0`
- cached `eI`
- cached `corr`
- cached final ratio

---

## 11. Denominator audit

The V2 denominator audit separates generic Schur-recurrence denominators from
the few denominators that require explicit interval sign checks.

The recurrence family can be handled by generic invariants of the form:

```text
|κ| < 1
|u| < 1
0 < p < 1
```

from which denominator positivity / nonvanishing follows.

Therefore millions of individual denominator intervals do not need to become
proof inputs.

Individual exact sign checks remain necessary for:

```text
r_n + pi1
similarity scale
rho
```

Any recorded worst-case interval or count remains diagnostic only.

---

## 12. C0 precision audit

The V2 audit identified three distinct center matrices used at different
effective precisions:

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

The conservative exact-replay design uses:

```text
Bridge
  = C0_delta - C0_residual

eI_total
  = eI_semantic + ‖B * Bridge‖∞

final_ratio
  = e0 + eI_total + corr
```

`Bridge` and `‖B * Bridge‖∞` must be recomputed from exact proof data, not
trusted as summaries.

`C0_precond` is not required in the minimal finite proof payload if `B` is
treated as an arbitrary witness whose adequacy is checked by the downstream
exact inequalities.

A separate audit is evaluating whether a single canonical exact center
Jacobian can be regenerated directly by the checker, potentially eliminating
the need to export historical midpoint matrices entry-by-entry.

---

## 13. Payload-size audit

A conservative historical-matrix payload would require both `C0_delta` and
`C0_residual`.

Each currently has approximately:

```text
5,128,003 lower-triangular entries
```

The conservative payload estimate is approximately:

```text
50–56 GB uncompressed
24–35 GB compressed
```

This is considered a conservative design, not yet the preferred final form.

A current audit is testing whether the checker can regenerate a canonical
reference matrix from compact exact inputs and thereby reduce the proof-object
size substantially.

Single-document JSON storage is not considered appropriate for the
conservative payload; row-range sharding would be required.

---

## 14. Analytic-source trust boundary

Exporting Arb interval endpoints as exact dyadics does not establish inside
Lean that the corresponding transcendental functions actually lie in those
intervals.

The following remain external analytic-source obligations at this stage:

- Riemann zeta enclosures
- zeta log-derivative enclosures
- logarithmic source terms
- Euler–Mascheroni constant terms
- other transcendental source evaluations used by the certificate

The finite exact checker may initially treat these intervals as explicit
external inputs.

A later analytic-source bridge is required for full kernel trust.

---

## 15. Current design / audit artifacts

The certificate audit currently includes documents such as:

```text
DATAFLOW_MAP.md
EXPORT_SCHEMA.md
EXACT_EXPORT_PATCH.md
DENOMINATOR_REDUCTION.md
V2_PROOF_OBLIGATIONS.md
C0_PRECISION_BRIDGE.md
V2_MINIMAL_PROOF_PAYLOAD.md
```

These documents describe design, provenance, trust boundaries, and replay
obligations.

They do not themselves remove the project-specific Lean axiom.

---

## 16. Current trust summary

```text
Lean source build:
PASS locally

Major audited Lean theorem dependencies:
[propext, Classical.choice, Quot.sound]

xi zero → R_boundary pole:
KERNEL-CHECKED

R_boundary Nevanlinna membership:
OPEN — reduced to digamma growth

h_interpolant elimination:
OPEN — final Montel / rigidity integration

Finite prefix through N = 4052:
EXTERNALLY CERTIFIED

Project-specific certificate axiom:
PRESENT

V2 numerical regression:
PASS

V2 exact-export:
RUNNING

V3 exact-export:
NOT STARTED

Arb-free full V2 exact replay:
PENDING

Lean finite-certificate checker:
NOT YET IMPLEMENTED

Analytic-source bridge:
OPEN

Full end-to-end kernel verification:
NOT YET COMPLETE
```

---

## 17. Audit interpretation

The present state should be interpreted as follows:

- a substantial portion of the analytic proof architecture is formalized and
  kernel-checked;
- the finite computational prefix has an independently reproduced external
  certificate;
- the finite certificate is not yet fully represented as a Lean-kernel-checked
  proof object;
- the main remaining analytic bridge is the digamma-growth obligation for
  `R_boundary`;
- the main remaining computational bridge is conversion of the external Arb
  certificate into independently replayable exact proof data and then a Lean
  checker;
- the analytic correctness of Arb-generated transcendental source intervals
  remains a separate trust obligation.

The project therefore does not currently claim full end-to-end kernel
verification of the Riemann Hypothesis argument.
