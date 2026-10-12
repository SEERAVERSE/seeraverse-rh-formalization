# SEERAVERSE Riemann Hypothesis Formalization

Human-directed, AI-assisted, Lean-verified research.

This repository contains the Lean 4 / Mathlib formalization, audit infrastructure,
and certificate-verification work for the SEERAVERSE Riemann Hypothesis research
program.

> **Current status:** this repository does **not** claim a complete end-to-end
> kernel-verified proof of the Riemann Hypothesis. Substantial components are
> kernel-checked, while remaining analytic and certificate trust boundaries are
> tracked explicitly in `STATUS.md` and `AUDIT.md`.

## Scope

The project currently develops and audits:

- finite Nevanlinna–Pick interpolation
- Schur reduction and positive-semidefinite matrix transport
- inverse Schur reconstruction
- Montel / normal-family compactness
- Jensen / non-Blaschke rigidity
- meromorphic continuation and pole exclusion
- the `xi`-zero → `R_boundary`-pole mechanism
- exact computational-certificate replay
- Lean integration of finite certificate checks

The objective is not merely to obtain a compiling top-level theorem. The
objective is to make the dependency chain explicit and progressively move each
remaining trust boundary into machine-checkable form.

## Build

Main target:

```text
SEERAVERSE.MainChain
```

Latest verified local build:

```text
lake build SEERAVERSE.MainChain
Build completed successfully (8965 jobs).
```

GitHub Actions CI also passes on a GitHub-hosted Ubuntu runner.

The current workflow may emit a non-fatal cache-save warning from `/usr/bin/tar`;
the Lean build itself completes successfully.

## Verification policy

The project follows these rules:

- no `sorry` in completed proof blocks
- no silent promotion of external numerical output to Lean theorem
- no new project-specific axioms to hide open obligations
- diagnostic PASS flags are not proof inputs
- external numerical certificates must be independently replayable
- finite exact arithmetic and analytic-source trust are audited separately
- high-level `#print axioms` output is interpreted together with theorem
  hypotheses and external dependencies

## Current certificate status

The V2 exact replay is closed:

```text
Gate A: PASS
Gate B: PASS
Gate C: PASS
Gate D: PASS
Gate E: PASS
Gate F: PASS
Gate G: PASS
Gate H: PASS

V2 exact replay: PASS
```

The exact contraction replay proves a strict ratio `< 1` using exact
integer/dyadic arithmetic.

The V3 extension for `3204..4052` is currently being exported into an exact
proof-object form and will be independently replayed before Lean replacement.

The project-specific Lean axiom

```lean
Certificate4052.certificate_freshPivotResidual_positive
```

is still present and has **not yet** been removed.

## Current analytic obligations

Two major analytic items remain separate from the V2 exact finite replay:

1. `IsNevanlinnaOn R_boundary farRightHalfPlane`, currently reduced to a
   complex digamma growth estimate.

2. The analytic-source bridge for finite certificate source intervals. The
   current audit has reduced the key zeta-log-derivative tail requirement to
   an explicit uniform bound over odd integers `s = 3, 5, ..., 8107`.

See `STATUS.md` for the current project state and `AUDIT.md` for trust-boundary
details.

## Repository documents

- `README.md` — stable project overview
- `STATUS.md` — current project state
- `AUDIT.md` — verification policy, trust boundaries, hashes, and audit details

## Licensing

Code, Lean sources, checkers, and scripts in this repository are licensed under
the BSD 3-Clause License; see `LICENSE`.

Documentation, explanatory text, research notes, status documents, and audit
documents are licensed under the Creative Commons Attribution 4.0 International
License (CC BY 4.0), unless otherwise noted; see `LICENSE-DOCS`.

Copyright © 2026 SEERAVERSE Research Initiative Inc.
