# SEERAVERSE Riemann Hypothesis Formalization

Human-directed, AI-assisted, Lean-verified research.

This repository contains the Lean 4 / Mathlib formalization and audit
infrastructure for the SEERAVERSE Riemann Hypothesis research program.

The project focuses on:

- finite Nevanlinna–Pick interpolation
- Schur reduction and positive-semidefinite matrix arguments
- Montel / normal-family compactness
- Jensen and non-Blaschke rigidity
- meromorphic continuation and pole exclusion
- computational certificate verification

## Status

This is an active formalization project.

Several major components of the proposed proof architecture have been
formalized and kernel-checked, while additional analytic and computational
verification obligations remain under active development.

Detailed status and audit information will be maintained separately in:

- `STATUS.md`
- `AUDIT.md`

## Verification policy

The project distinguishes between:

- Lean-kernel-checked theorems
- external computational certificates
- remaining analytic obligations
- project-specific assumptions or axioms still under audit

Successful compilation alone is not treated as proof of an unformalized
mathematical step.

## Technology

- Lean 4
- Mathlib
- Lake

## Research approach

Human-directed, AI-assisted, Lean-verified.

AI systems are used extensively for proof exploration, implementation,
code generation, and audit support. Final formal claims are accepted only
when checked by the Lean kernel or explicitly marked as external obligations.

## Organization
SEERAVERSE Research Initiative

https://seeraverse.com
