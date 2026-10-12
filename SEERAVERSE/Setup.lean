import Mathlib

/-!
  SEERAVERSE — Setup.lean
  =======================
  Phase A: Formalization of Section 2 of the paper (the boundary function
  and notation).

  This file introduces the central objects of the paper in the centered
  critical-line coordinate, and proves the first conservative identities
  that follow from the functional equation and the factorization of the
  completed zeta function:

    * The completed Riemann zeta function `Λ(s)` and the entire function
      `ξ(s) = (1/2) · s · (s - 1) · Λ(s)`.
    * The centered coordinate `s = 1/2 + x`, the distinguished values
      `a = 5/2` (so `s = 3`) and `c = 1/2`.
    * `C(x) = (Λ'/Λ)(1/2 + x)`, `A = C(5/2) = (Λ'/Λ)(3)`.
    * The boundary normalization constant `κ = 1 + (6/5)·A`.
    * The boundary-first transform `R_∂(x)` (paper equation (2.1)).
    * The squared critical-line coordinate `Ξ(u) = ξ(1/2 + √u)`,
      `m(u) = (Ξ'/Ξ)(u)`, `Φ(u) = (u - c²)·m(u)` (paper §2.2).

  Proven identities (paper §2):
    * `A = (Λ'/Λ)(3)`                          (definition)
    * `6 · (A + 5/6) = 5 · κ`                  (algebra, §2.1)
    * `ξ(s) = ξ(1 - s)`                        (functional equation)
    * `(ξ'/ξ)(s) = (Λ'/Λ)(s) + 1/s + 1/(s-1)`  (factorization)

  Next targets (paper §2.1–2.3):
    * `(ξ'/ξ)(1 - s) = -(ξ'/ξ)(s)`             (symmetry)
    * `(ξ'/ξ)(3) = A + 5/6`                    (cancellation at s = 3)
    * `R_∂(-x) = -R_∂(x)`                      (oddness, paper eq (2.2))
    * `R_∂(√u)/√u = 2·(Φ(u) - Φ(a²))/(u - a²)` (secant, paper eq (2.3))

  Conventions: match the rest of the project (`import Mathlib`, namespace
  `SEERAVERSE`, doc comments in English, lemmas named after the statement).
-/

open Complex

namespace SEERAVERSE
noncomputable section


/-! ## Section 2 definitions -/

/-- The completed Riemann zeta function `Λ(s) = π^(-s/2) Γ(s/2) ζ(s)`,
    taken as the Mathlib definition `completedRiemannZeta`. It satisfies
    the functional equation `Λ(s) = Λ(1 - s)`. -/
def Lambda (s : ℂ) : ℂ := completedRiemannZeta s

/-- The entire function `ξ(s) = (1/2) · s · (s - 1) · Λ(s)`. -/
def xi (s : ℂ) : ℂ := (1/2) * s * (s - 1) * Lambda s

/-- The distinguished value `a = 5/2` (the centered coordinate of `s = 3`). -/
def a : ℂ := 5/2

/-- The half-width `c = 1/2` (so `c^2 = 1/4`). -/
def c : ℂ := 1/2

/-- `C(x) = (Λ'/Λ)(1/2 + x)`, the logarithmic derivative of the completed
    zeta in the centered coordinate. -/
def C (x : ℂ) : ℂ := logDeriv Lambda (1/2 + x)

/-- `A = C(5/2) = (Λ'/Λ)(3)`, the value of the logarithmic derivative at
    the distinguished point `s = 3`. -/
def A : ℂ := C (5/2)

/-- The fixed boundary-normalization constant `κ = 1 + (6/5)·A`
    (paper §2.1). It is precisely the value that removes the apparent
    singularity of `R_∂` at `s = 3`. -/
def kappa : ℂ := 1 + (6/5) * A

/-- The boundary-first transform `R_∂(x)` (paper equation (2.1)):
    `R_∂(x) = [s(s-1)·(ξ'/ξ)(s) - κ(2s-1)] / [(s-3)(s+2)]` with `s = 1/2 + x`.
    The choice of `κ` makes the numerator vanish at `s = 3` together with the
    denominator factor, so the apparent singularity at `x = a = 5/2` is
    removable (in Lean the quotient is simply evaluated, giving `0` there). -/
def R_boundary (x : ℂ) : ℂ :=
  let s := 1/2 + x
  (s * (s - 1) * logDeriv xi s - kappa * (2 * s - 1)) / ((s - 3) * (s + 2))

/-- The squared critical-line coordinate (paper §2.2):
    `Ξ(u) = ξ(1/2 + √u)`. Because `x ↦ ξ(1/2 + x)` is even, this is
    independent of the choice of square-root branch. -/
def Xi (u : ℂ) : ℂ := xi (1/2 + sqrt u)

/-- `m(u) = (Ξ'/Ξ)(u)`, the logarithmic derivative of `Ξ`. -/
def m (u : ℂ) : ℂ := logDeriv Xi u

/-- `Φ(u) = (u - c²)·m(u)`, with `c² = 1/4` (paper §2.2). -/
def Phi (u : ℂ) : ℂ := (u - c^2) * m u

/-! ## 2.1  Basic identities -/

/-- `A = C(5/2)`, by definition (centered coordinate of `s = 3`). -/
theorem A_def : A = C (5/2) := rfl

/-- `A = (Λ'/Λ)(3)`: at `x = 5/2` the centered coordinate is `s = 3`. -/
theorem A_eq_logDeriv_Lambda_3 : A = logDeriv Lambda 3 :=
  calc
    A = C (5/2) := A_def
    _ = logDeriv Lambda (1/2 + 5/2) := rfl
    _ = logDeriv Lambda 3 := by norm_num

/-- `6 · (A + 5/6) = 5 · κ` (paper §2.1, `κ = 1 + (6/5)·A`). -/
theorem kappa_algebra : 6 * (A + 5/6) = 5 * kappa :=
  calc
    6 * (A + 5/6) = 6 * A + 6 * (5/6) := by ring
    _ = 6 * A + 5 := by norm_num
    _ = 5 + 6 * A := by ring
    _ = 5 * (1 + (6/5) * A) := by ring
    _ = 5 * kappa := by rw [kappa]

/-- The functional equation of the completed zeta: `Λ(s) = Λ(1 - s)`. -/
theorem Lambda_symmetry (s : ℂ) : Lambda s = Lambda (1 - s) := by
  rw [Lambda, Lambda]
  exact (completedRiemannZeta_one_sub s).symm

/-- The functional equation of `ξ`, `ξ(s) = ξ(1 - s)`, which follows from the
    functional equation of `Λ` together with the involution `s ↦ 1 - s`
    interchanging the factors `s` and `s - 1`. -/
theorem xi_symmetry (s : ℂ) : xi s = xi (1 - s) := by
  calc
    xi s = (1/2) * s * (s - 1) * Lambda s := rfl
    _ = (1/2) * (1 - s) * ((1 - s) - 1) * Lambda s := by ring
    _ = (1/2) * (1 - s) * ((1 - s) - 1) * Lambda (1 - s) := by rw [Lambda_symmetry s]
    _ = xi (1 - s) := rfl

/-- `logDeriv` of a product is the sum of the `logDeriv`s, used to factor the
    logarithmic derivative of `ξ`: `(ξ'/ξ)(s) = (Λ'/Λ)(s) + 1/s + 1/(s - 1)`.
    This holds on the domain where `Λ(s) ≠ 0` (hence `ξ(s) ≠ 0`). -/
theorem logDeriv_xi_factor (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hL : Lambda s ≠ 0) :
    logDeriv xi s = logDeriv Lambda s + 1 / s + 1 / (s - 1) := by
  -- `s - 1 ≠ 0` from `s ≠ 1`.
  have hs1' : s - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hs1 h
  -- Write `xi` as a scalar multiple of `t ↦ t * (t - 1) * Λ t`, so the constant
  -- `(1/2)` can be pulled out of the log-derivative.
  have hxi : xi = fun t : ℂ => (1/2) * (t * (t - 1) * Lambda t) := by
    funext t
    rw [xi]
    ring
  rw [hxi]
  have hconst : logDeriv (fun t : ℂ => (1/2) * (t * (t - 1) * Lambda t)) s
      = logDeriv (fun t : ℂ => t * (t - 1) * Lambda t) s :=
    logDeriv_const_mul s (1/2) (by norm_num)
  rw [hconst]
  -- Split `t * (t - 1) * Λ t` into the product `(t * (t - 1)) * Λ` and use the
  -- product rule for `logDeriv`.
  have hsplit : (fun t : ℂ => t * (t - 1) * Lambda t) = (fun t : ℂ => t * (t - 1)) * Lambda := by
    funext t
    rfl
  rw [hsplit]
  have hfgns : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1'
  have hdiff_f : DifferentiableAt ℂ (fun t : ℂ => t * (t - 1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub (differentiableAt_const (1 : ℂ)))
  have hdiff_L : DifferentiableAt ℂ Lambda s := differentiableAt_completedZeta hs0 hs1
  have hsum : logDeriv ((fun t : ℂ => t * (t - 1)) * Lambda) s
      = logDeriv (fun t : ℂ => t * (t - 1)) s + logDeriv Lambda s :=
    logDeriv_mul s hfgns hL hdiff_f hdiff_L
  rw [hsum]
  -- Split `t * (t - 1)` into `id * (fun t => t - 1)` and apply the product rule
  -- again.
  have hsplit2 : (fun t : ℂ => t * (t - 1)) = id * (fun t : ℂ => t - 1) := by
    funext t
    rfl
  rw [hsplit2]
  have hsum2 : logDeriv (id * (fun t : ℂ => t - 1)) s
      = logDeriv id s + logDeriv (fun t : ℂ => t - 1) s :=
    logDeriv_mul s hs0 hs1' differentiableAt_id
      (differentiableAt_id.sub (differentiableAt_const (1 : ℂ)))
  rw [hsum2]
  rw [logDeriv_id]
  -- The affine part: `logDeriv (fun t => t - 1) s = 1 / (s - 1)`.
  have haffine : logDeriv (fun t : ℂ => t - 1) s = 1 / (s - 1) := by
    have hd : deriv (fun t : ℂ => t - 1) s = 1 := by
      have hsub : (fun t : ℂ => t - 1) = id - (fun _ : ℂ => 1) := by
        funext t
        rfl
      rw [hsub]
      rw [deriv_sub differentiableAt_id (differentiableAt_const (1 : ℂ))]
      simp [deriv_id, deriv_const]
    rw [logDeriv_apply (fun t : ℂ => t - 1) s, hd]
  rw [haffine]
  -- Both sides are the same summands reordered.
  ring

/-- Symmetry of the logarithmic derivative, from the functional equation:
    `(ξ'/ξ)(1 - s) = -(ξ'/ξ)(s)`.
    Since `ξ` is invariant under `s ↦ 1 - s`, differentiating the identity
    `ξ(s) = ξ(1 - s)` and applying the chain rule gives
    `ξ'(s) = -ξ'(1 - s)`; dividing by `ξ(s) = ξ(1 - s)` (with Lean's
    convention `x / 0 = 0`, so the identity also holds at zeros of `ξ`)
    yields the claim. -/
theorem xi_logDeriv_symmetry (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv xi (1 - s) = -(logDeriv xi s) := by
  -- `1 - s` is also away from the singular points `0` and `1`.
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    exact hs1 (sub_eq_zero.mp h).symm
  have h1s1 : 1 - s ≠ 1 := by
    intro h
    have : s = 0 := by
      have : (1 - s) - 1 = 0 := by simpa using h
      simpa using ‹(1 - s) - 1 = 0›
    exact hs0 ‹s = 0›
  -- `ξ` is differentiable at `1 - s`.
  have hdiff_1s : DifferentiableAt ℂ xi (1 - s) :=
    (differentiableAt_const (1/2 : ℂ)).mul differentiableAt_id
      |>.mul (differentiableAt_id.sub (differentiableAt_const (1 : ℂ)))
      |>.mul (differentiableAt_completedZeta h1s0 h1s1)
  -- The functional equation as an equality of functions: `ξ = ξ ∘ (t ↦ 1 - t)`.
  have hfe : xi = (fun t : ℂ => xi (1 - t)) := by
    funext t
    exact xi_symmetry t
  -- Chain rule: `deriv (ξ ∘ (· ↦ 1 - ·)) s = ξ'(1 - s) · (-1)`.
  have hderiv_affine : deriv (fun t : ℂ => 1 - t) s = -1 := by
    have hsub : (fun t : ℂ => 1 - t) = (fun _ : ℂ => 1) - id := by
      funext t
      rfl
    rw [hsub]
    rw [deriv_sub (differentiableAt_const (1 : ℂ)) differentiableAt_id]
    simp [deriv_const, deriv_id]
  have hderiv_comp : deriv (xi ∘ (fun t : ℂ => 1 - t)) s = deriv xi (1 - s) * (-1) := by
    have h := deriv_comp s hdiff_1s (by fun_prop)
    rw [hderiv_affine] at h
    exact h
  -- `ξ ∘ (· ↦ 1 - ·) = fun t ↦ ξ(1 - t)`.
  have hfe' : (xi ∘ (fun t : ℂ => 1 - t)) = (fun t : ℂ => xi (1 - t)) := by
    funext t
    rfl
  have hderiv_neg : deriv (fun t : ℂ => xi (1 - t)) s = -(deriv xi (1 - s)) := by
    rw [← hfe', hderiv_comp]
    ring
  -- By the functional equation, the two derivatives are negatives.
  have hderiv_s : deriv xi s = -(deriv xi (1 - s)) := by
    have : deriv xi s = deriv (fun t : ℂ => xi (1 - t)) s := congrArg (fun f => deriv f s) hfe
    rw [this]
    exact hderiv_neg
  -- Unfold `logDeriv` (= `deriv f x / f x`) on both sides and rearrange.
  rw [logDeriv_apply xi (1 - s), logDeriv_apply xi s, hderiv_s, xi_symmetry s]
  ring

/-- Cancellation at `s = 3`: `(ξ'/ξ)(3) = (Λ'/Λ)(3) + 1/3 + 1/2 = A + 5/6`.
    In particular `6 · (ξ'/ξ)(3) = 5 · κ`, the paper's equation (2.1). -/
theorem xi_logDeriv_at_3 : logDeriv xi 3 = A + 5/6 := by
  -- `Λ(3) ≠ 0`, since `riemannZeta 3 ≠ 0` and `riemannZeta s = Λ s / Γ(s/2)`
  -- for `s ≠ 0`.
  have hL3 : Lambda 3 ≠ 0 := by
    intro h
    have h' : completedRiemannZeta 3 = 0 := by simpa [Lambda] using h
    have : riemannZeta 3 = 0 := by
      rw [riemannZeta_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0), h']
      simp
    exact (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (3 : ℂ).re)) this
  rw [logDeriv_xi_factor (s := 3) (by norm_num) (by norm_num) hL3]
  rw [← A_eq_logDeriv_Lambda_3]
  ring

/-- `6 · (ξ'/ξ)(3) = 5 · κ` (paper §2.1: the value of `κ` is exactly what
    removes the apparent singularity of `R_∂` at `s = 3`). -/
theorem xi_logDeriv_at_3_kappa : 6 * logDeriv xi 3 = 5 * kappa := by
  rw [xi_logDeriv_at_3]
  exact kappa_algebra

/-- The boundary transform is odd in the centered coordinate
    (paper equation (2.2)): `R_∂(-x) = -R_∂(x)`, wherever the
    logarithmic derivative is defined on both sides. -/
theorem R_boundary_odd (x : ℂ) (hs0 : 1 / 2 + x ≠ 0) (hs1 : 1 / 2 + x ≠ 1) :
    R_boundary (-x) = -(R_boundary x) := by
  -- Logarithmic-derivative symmetry with `s = 1/2 + x` and `t = 1 - s = 1/2 - x`.
  have hsym : logDeriv xi (1/2 + -x) = -(logDeriv xi (1/2 + x)) := by
    have h1 : 1/2 + -x = 1 - (1/2 + x) := by ring
    rw [h1]
    exact xi_logDeriv_symmetry (1/2 + x) hs0 hs1
  -- The denominator is invariant under `x ↦ -x` (both equal `x^2 - 25/4`).
  have hD : (1/2 + -x - 3) * (1/2 + -x + 2) = (1/2 + x - 3) * (1/2 + x + 2) := by
    ring
  simp only [R_boundary]
  rw [hsym, hD]
  ring

/-! ## 2.3  Secant identity (paper eq. (2.3)) -/

/-- Chain rule: for `u` in the slit plane with `1/2 + √u` away from `0` and `1`,
    `m u = (1/(2·√u)) · (ξ'/ξ)(1/2 + √u)`.
    This follows from `Ξ(u) = ξ(1/2 + √u)` and the chain rule
    `deriv Ξ u = ξ'(1/2+√u) · (1/(2√u))`. -/
theorem m_chain (u : ℂ) (hslit : u ∈ slitPlane)
    (hs0 : 1 / 2 + sqrt u ≠ 0) (hs1 : 1 / 2 + sqrt u ≠ 1) :
    m u = (1 / (2 * sqrt u)) * logDeriv xi (1/2 + sqrt u) := by
  have hXi : Xi = (fun v : ℂ => xi (1/2 + sqrt v)) := by funext v; rfl
  simp only [m, hXi, logDeriv_apply]
  -- Goal: deriv (fun v => xi (1/2 + sqrt v)) u / xi (1/2 + sqrt u)
  --       = (1 / (2 * sqrt u)) * deriv xi (1/2 + sqrt u) / xi (1/2 + sqrt u)
  have hcomp : (fun v : ℂ => xi (1/2 + sqrt v)) = xi ∘ (fun v : ℂ => 1/2 + sqrt v) := by
    funext v; rfl
  rw [hcomp]
  have hdiff_inner : DifferentiableAt ℂ (fun v : ℂ => 1/2 + sqrt v) u := by fun_prop
  have hdiff_xi : DifferentiableAt ℂ xi (1/2 + sqrt u) := by
    have hxi : xi = (fun t : ℂ => (1/2) * t * (t - 1) * Lambda t) := by
      funext t
      rw [xi]
    rw [hxi]
    have hsplit : (fun t : ℂ => (1/2) * t * (t - 1) * Lambda t) =
        (fun t : ℂ => (1/2) * t * (t - 1)) * Lambda := by
      funext t
      simp [Lambda]
    rw [hsplit]
    have hdiff_poly : DifferentiableAt ℂ (fun t : ℂ => (1/2) * t * (t - 1)) (1/2 + sqrt u) := by fun_prop
    have hdiff_L : DifferentiableAt ℂ Lambda (1/2 + sqrt u) := differentiableAt_completedZeta hs0 hs1
    exact hdiff_poly.mul hdiff_L
  have hcomp_deriv : deriv (xi ∘ (fun v : ℂ => 1/2 + sqrt v)) u =
      deriv xi (1/2 + sqrt u) * deriv (fun v : ℂ => 1/2 + sqrt v) u := by
    have hinner' : HasDerivAt (fun v : ℂ => 1/2 + sqrt v) (deriv (fun v : ℂ => 1/2 + sqrt v) u) u :=
      hdiff_inner.hasDerivAt
    have hxi' : HasDerivAt xi (deriv xi (1/2 + sqrt u)) (1/2 + sqrt u) :=
      hdiff_xi.hasDerivAt
    exact (HasDerivAt.comp u hxi' hinner').deriv
  rw [hcomp_deriv]
  -- Compute deriv (fun v => 1/2 + sqrt v) u = deriv sqrt u = u^(-1/2)/2 = 1/(2*sqrt u)
  have hinner : deriv (fun v : ℂ => 1/2 + sqrt v) u = 1 / (2 * sqrt u) := by
    have h : (fun v : ℂ => (1/2 : ℂ) + sqrt v) = (fun _ : ℂ => (1/2 : ℂ)) + sqrt := by
      funext v
      rfl
    rw [h]
    rw [deriv_add (differentiableAt_const (1/2 : ℂ)) (differentiableAt_sqrt hslit)]
    simp [deriv_const]
    rw [deriv_sqrt hslit]
    have hcpow : u ^ (-1/2 : ℂ) / 2 = 1 / (2 * sqrt u) := by
      have h : (-1/2 : ℂ) = -(2⁻¹ : ℂ) := by norm_num
      rw [h, cpow_neg u (2⁻¹ : ℂ), Complex.sqrt]
      field_simp
    rw [hcpow]
    field_simp
  rw [hinner]
  simp
  ring

/-- `Φ(a²) = κ`: the value of `Φ` at the distinguished point `a² = 25/4`
    equals the boundary-normalization constant `κ = 1 + (6/5)·A`.
    Computation: `Φ(a²) = (a²-c²)·m(a²) = 6 · (1/5)·(ξ'/ξ)(3) = (6/5)·(ξ'/ξ)(3)`,
    and `κ = 1 + (6/5)·A = (6/5)·(A + 5/6) = (6/5)·(ξ'/ξ)(3)`. -/
theorem Phi_a2_eq_kappa : Phi (a^2) = kappa := by
  have ha2 : (a^2 : ℂ) = 25/4 := by simp [a]; norm_num
  have hc2 : (c^2 : ℂ) = 1/4 := by simp [c]; norm_num
  have hslit : (a^2 : ℂ) ∈ slitPlane := by
    rw [ha2]
    simp [slitPlane]
  have hsq : sqrt (a^2 : ℂ) = 5/2 := by
    rw [ha2, Complex.sqrt]
    have h3 : (5/2 : ℂ) ^ 2 = (25/4 : ℂ) := by norm_num
    rw [← h3]
    exact sq_cpow_two_inv (x := (5/2 : ℂ)) (by norm_num)
  have hs0 : 1/2 + sqrt (a^2 : ℂ) ≠ 0 := by
    rw [hsq]
    norm_num
  have hs1 : 1/2 + sqrt (a^2 : ℂ) ≠ 1 := by
    rw [hsq]
    norm_num
  have hm : m (a^2) = (1 / (2 * sqrt (a^2 : ℂ))) * logDeriv xi (1/2 + sqrt (a^2 : ℂ)) :=
    m_chain (a^2) hslit hs0 hs1
  rw [Phi, hm, hsq]
  rw [ha2, hc2]
  have h3 : (1/2 + 5/2 : ℂ) = 3 := by norm_num
  rw [h3]
  norm_num
  have hlog : logDeriv xi 3 = A + 5/6 := xi_logDeriv_at_3
  rw [hlog]
  rw [kappa]
  ring

/-- Secant identity (paper equation (2.3)):
    `R_∂(√u)/√u = 2·[Φ(u) − Φ(a²)]/(u − a²)`.
    For `u` in the slit plane with `s = 1/2 + √u` away from the singular
    points `0` and `1`. -/
theorem secant_identity (u : ℂ) (hslit : u ∈ slitPlane)
    (hs0 : 1 / 2 + sqrt u ≠ 0) (hs1 : 1 / 2 + sqrt u ≠ 1) :
    R_boundary (sqrt u) / sqrt u = 2 * (Phi u - Phi (a^2)) / (u - a^2) := by
  -- `u ∈ slitPlane` implies `u ≠ 0` and `sqrt u ≠ 0`.
  have hu : u ≠ 0 := by
    intro h
    simp [h, slitPlane] at hslit
    <;> contradiction
  have hsu : sqrt u ≠ 0 := by
    intro h
    have h2 : u = 0 := by
      have h3 : (sqrt u) ^ 2 = u := by
        rw [Complex.sqrt]
        exact cpow_nat_inv_pow u (show (2 : ℕ) ≠ 0 by decide)
      rw [← h3, h]
      norm_num
    contradiction
  -- Unfold R_boundary with x = sqrt u, so s = 1/2 + sqrt u.
  simp only [R_boundary]
  -- Algebraic simplifications:
  -- (1/2 + √u)(√u - 1/2) = u - 1/4 = u - c²
  have hnum1 : (1/2 + sqrt u) * (1/2 + sqrt u - 1) = u - c^2 := by
    have h : (1/2 + sqrt u) * (1/2 + sqrt u - 1) = (1/2 + sqrt u) * (sqrt u - 1/2) := by ring
    rw [h]
    have : (1/2 + sqrt u) * (sqrt u - 1/2) = (sqrt u) ^ 2 - (1/2 : ℂ) ^ 2 := by ring
    rw [this]
    have hsqr : (sqrt u) ^ 2 = u := by
      rw [Complex.sqrt]
      exact cpow_nat_inv_pow u (show (2 : ℕ) ≠ 0 by decide)
    rw [hsqr]
    simp [c]
  -- 2*(1/2 + √u) - 1 = 2√u
  have hnum2 : 2 * (1/2 + sqrt u) - 1 = 2 * sqrt u := by ring
  -- (√u - 5/2)(√u + 5/2) = u - 25/4 = u - a²
  have hden : (1/2 + sqrt u - 3) * (1/2 + sqrt u + 2) = u - a^2 := by
    have h1 : 1/2 + sqrt u - 3 = sqrt u - 5/2 := by ring
    have h2 : 1/2 + sqrt u + 2 = sqrt u + 5/2 := by ring
    rw [h1, h2]
    have : (sqrt u - 5/2) * (sqrt u + 5/2) = (sqrt u) ^ 2 - (5/2 : ℂ) ^ 2 := by ring
    rw [this]
    have hsqr : (sqrt u) ^ 2 = u := by
      rw [Complex.sqrt]
      exact cpow_nat_inv_pow u (show (2 : ℕ) ≠ 0 by decide)
    rw [hsqr]
    simp [a]
  rw [hnum1, hnum2, hden]
  -- Use the chain rule: logDeriv xi (1/2 + √u) = 2·√u · m u
  have hchain : logDeriv xi (1/2 + sqrt u) = 2 * sqrt u * m u := by
    have h := m_chain u hslit hs0 hs1
    rw [h]
    field_simp [hsu]
  rw [hchain]
  -- Simplify: (u - c²)·(2√u·m u) - κ·2√u = 2√u·((u-c²)·m u - κ)
  -- and 2√u·((u-c²)·m u - κ)/(u-a²)/√u = 2·((u-c²)·m u - κ)/(u-a²)
  -- = 2·(Φ(u) - κ)/(u - a²) = 2·(Φ(u) - Φ(a²))/(u - a²)
  have hPhi : (u - c^2) * m u = Phi u := by
    simp [Phi]
  field_simp [hsu]
  rw [hPhi, Phi_a2_eq_kappa]

/-- Secant identity (sqrt-free form, paper §2.3 restated in the centered
    coordinate `x`):
    `R_∂(x)/x = 2·[Φ(x²) − Φ(a²)]/(x² − a²)`.
    This is the same identity as `secant_identity` with `u = x²` and
    `√u = x` (i.e. `x` in the principal branch, `x.re ≥ 0`). -/
theorem secant_identity_sqrtfree (x : ℂ) (hsqr : sqrt (x^2) = x)
    (hslit : x^2 ∈ slitPlane)
    (hs0 : 1/2 + x ≠ 0) (hs1 : 1/2 + x ≠ 1) :
    R_boundary x / x = 2 * (Phi (x^2) - Phi (a^2)) / (x^2 - a^2) := by
  have h := secant_identity (x^2) hslit (by rw [hsqr]; exact hs0) (by rw [hsqr]; exact hs1)
  rw [hsqr] at h
  exact h


end
end SEERAVERSE
