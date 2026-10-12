import Mathlib
import SEERAVERSE.Setup

/-!
# Pole exclusion and RH conclusion (paper Section 10)

This module formalizes Section 10 of the paper:
1. Definition of `HasPoleAt` for complex functions.
2. The residue multiplier `residue_factor(ρ) = ρ(ρ - 1) / ((ρ - 3)(ρ + 2))`
   for a potential pole at `x = ρ - 1/2`.
3. Proof that `residue_factor(ρ) ≠ 0` for any critical-strip point `0 < ℜ ρ < 1`.
4. The pole exclusion theorem: Holomorphicity of `R_∂` on `ℜ x > 0` implies
   that no nontrivial zero `ρ` of `ξ` can lie off the critical line `ℜ ρ = 1/2`.
-/

namespace SEERAVERSE
namespace PoleExclusion

open Complex

noncomputable section

/-- A function `f : ℂ → ℂ` has a pole at `z₀` if `‖f z‖ → ∞` as `z → z₀` (`z ≠ z₀`). -/
def HasPoleAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin z₀ {z₀}ᶜ) Filter.atTop

/-- The residue multiplier at `x = ρ - 1/2` produced by a zero `ρ` of `ξ` (paper eq 10.1):
    `residue_factor(ρ) = ρ(ρ - 1) / ((ρ - 3)(ρ + 2))`. -/
def residue_factor (rho : ℂ) : ℂ :=
  rho * (rho - 1) / ((rho - 3) * (rho + 2))

/-- A globally analytic presentation of `xi`, with the apparent poles of `Lambda`
    cancelled explicitly. -/
def xiEntire (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

theorem xi_eq_entire (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = xiEntire s := by
  rw [xi, Lambda, completedRiemannZeta_eq]
  unfold xiEntire
  field_simp
  ring

/-- The completed `xi` function is entire. -/
theorem xiEntire_analytic : AnalyticOnNhd ℂ xiEntire Set.univ := by
  intro s _
  unfold xiEntire
  exact (analyticAt_const.mul
    (((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul
      (differentiable_completedZeta₀.analyticAt s)).add analyticAt_const))

/-- `xi` is not the zero entire function. -/
theorem xi_three_ne_zero : xi 3 ≠ 0 := by
  have hL3 : Lambda 3 ≠ 0 := by
    intro h
    have hz : riemannZeta 3 = 0 := by
      rw [riemannZeta_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0)]
      simp [Lambda] at h
      simp [h]
    exact (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (3 : ℂ).re)) hz
  rw [xi]
  norm_num
  exact hL3

/-- Every zero of `xi` has finite analytic (hence meromorphic) order. -/
theorem xi_meromorphicOrderAt_ne_top (rho : ℂ) : meromorphicOrderAt xi rho ≠ ⊤ := by
  intro htop
  have heq : xi =ᶠ[nhdsWithin rho {rho}ᶜ] xiEntire := by
    by_cases hrho0 : rho = 0
    · subst rho
      filter_upwards [self_mem_nhdsWithin,
        (eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
          with z hz0 hz1
      exact xi_eq_entire z (by simpa using hz0) hz1
    by_cases hrho1 : rho = 1
    · subst rho
      filter_upwards [self_mem_nhdsWithin,
        (eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)).filter_mono nhdsWithin_le_nhds]
          with z hz1 hz0
      exact xi_eq_entire z hz0 (by simpa using hz1)
    · filter_upwards [
        (eventually_ne_nhds hrho0).filter_mono nhdsWithin_le_nhds,
        (eventually_ne_nhds hrho1).filter_mono nhdsWithin_le_nhds] with z hz0 hz1
      exact xi_eq_entire z hz0 hz1
  have hev : xiEntire =ᶠ[nhdsWithin rho {rho}ᶜ] 0 := by
    filter_upwards [heq, meromorphicOrderAt_eq_top_iff.mp htop] with z he hzero
    simpa [← he] using hzero
  have hzero : xiEntire = fun _ : ℂ => 0 :=
    xiEntire_analytic.eq_of_frequently_eq (fun _ _ => analyticAt_const) hev.frequently
  have hxi3 : xi 3 = xiEntire 3 := xi_eq_entire 3 (by norm_num) (by norm_num)
  exact xi_three_ne_zero (hxi3.trans (congrFun hzero 3))

/-- The residue multiplier is non-zero for any point in the critical strip `0 < ℜ ρ < 1`. -/
theorem residue_factor_ne_zero (rho : ℂ) (hstrip : 0 < rho.re ∧ rho.re < 1) :
    residue_factor rho ≠ 0 := by
  unfold residue_factor
  apply div_ne_zero
  · apply mul_ne_zero
    · intro h0
      have : rho.re = 0 := by rw [h0, zero_re]
      linarith
    · intro h1
      have : (rho - 1).re = 0 := by rw [h1, zero_re]
      simp at this
      linarith
  · apply mul_ne_zero
    · intro h3
      have : (rho - 3).re = 0 := by rw [h3, zero_re]
      simp at this
      linarith
    · intro h2
      have : (rho + 2).re = 0 := by rw [h2, zero_re]
      simp at this
      linarith

/-- `xi` is analytic away from the two junk-value locations of `Lambda`. -/
theorem xi_analyticAt_of_ne_zero_one {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ xi s := by
  have hLambda : AnalyticAt ℂ Lambda s := by
    unfold Lambda
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
    exact differentiableAt_completedZeta hz0 hz1
  unfold xi Lambda
  exact (((analyticAt_const.mul analyticAt_id).mul
    (analyticAt_id.sub analyticAt_const)).mul
      hLambda)

private def poleCoefficient (x : ℂ) : ℂ :=
  let s := 1 / 2 + x
  s * (s - 1) / ((s - 3) * (s + 2))

private def poleRegular (x : ℂ) : ℂ :=
  let s := 1 / 2 + x
  0 - kappa * (2 * s - 1) / ((s - 3) * (s + 2))

private theorem R_boundary_eq_pole_decomposition :
    R_boundary = poleCoefficient * (logDeriv xi ∘ fun x => 1 / 2 + x) + poleRegular := by
  funext x
  simp only [R_boundary, poleCoefficient, poleRegular, Pi.add_apply, Pi.mul_apply,
    Function.comp_apply]
  ring

/-- A zero of `xi` in the critical strip produces a genuine pole of `R_boundary`. -/
theorem R_boundary_hasPoleAt_of_xi_zero (rho : ℂ) (hzero : xi rho = 0)
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    HasPoleAt R_boundary (rho - 1 / 2) := by
  let x₀ : ℂ := rho - 1 / 2
  have hrho0 : rho ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hstrip.1]
  have hrho1 : rho ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hstrip.2]
  have hrho3 : rho ≠ 3 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hstrip.2]
  have hrhom2 : rho ≠ -2 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hstrip.1]
  have hxiA : AnalyticAt ℂ xi rho := xi_analyticAt_of_ne_zero_one hrho0 hrho1
  have hxiM : MeromorphicAt xi rho := hxiA.meromorphicAt
  have hxiOrder0 : meromorphicOrderAt xi rho ≠ 0 := by
    rw [hxiA.meromorphicOrderAt_eq]
    simpa [hxiA.analyticOrderAt_ne_zero] using hzero
  have hlogOrder : meromorphicOrderAt (logDeriv xi) rho = -1 :=
    meromorphicOrderAt_logDeriv_eq_neg_one hxiM hxiOrder0
      (xi_meromorphicOrderAt_ne_top rho)
  have hxcenter : 1 / 2 + x₀ = rho := by
    dsimp [x₀]
    ring
  have hcompOrder :
      meromorphicOrderAt (logDeriv xi ∘ fun x : ℂ => 1 / 2 + x) x₀ = -1 := by
    have hderiv : deriv (fun x : ℂ => 1 / 2 + x) x₀ ≠ 0 := by
      simpa using (hasDerivAt_const x₀ (1 / 2 : ℂ)).add (hasDerivAt_id x₀) |>.deriv_ne_zero
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) hderiv, hxcenter]
    exact hlogOrder
  have hcoefA : AnalyticAt ℂ poleCoefficient x₀ := by
    unfold poleCoefficient
    apply AnalyticAt.div (by fun_prop) (by fun_prop)
    rw [hxcenter]
    exact mul_ne_zero (sub_ne_zero.mpr hrho3)
      (by simpa only [sub_neg_eq_add] using sub_ne_zero.mpr hrhom2)
  have hcoefNe : poleCoefficient x₀ ≠ 0 := by
    unfold poleCoefficient
    rw [hxcenter]
    exact residue_factor_ne_zero rho hstrip
  have hprincipalOrder :
      meromorphicOrderAt
        (poleCoefficient * (logDeriv xi ∘ fun x : ℂ => 1 / 2 + x)) x₀ = -1 := by
    rw [meromorphicOrderAt_mul_of_ne_zero hcoefA hcoefNe, hcompOrder]
  have hregularA : AnalyticAt ℂ poleRegular x₀ := by
    unfold poleRegular
    apply AnalyticAt.sub analyticAt_const
    apply AnalyticAt.div (by fun_prop) (by fun_prop)
    rw [hxcenter]
    exact mul_ne_zero (sub_ne_zero.mpr hrho3)
      (by simpa only [sub_neg_eq_add] using sub_ne_zero.mpr hrhom2)
  have hregularOrder : 0 ≤ meromorphicOrderAt poleRegular x₀ :=
    hregularA.meromorphicOrderAt_nonneg
  have hsumOrder : meromorphicOrderAt R_boundary x₀ = -1 := by
    rw [R_boundary_eq_pole_decomposition]
    have hlt : meromorphicOrderAt
        (poleCoefficient * (logDeriv xi ∘ fun x : ℂ => 1 / 2 + x)) x₀ <
        meromorphicOrderAt poleRegular x₀ := by
      rw [hprincipalOrder]
      apply lt_of_lt_of_le _ hregularOrder
      rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) by rfl]
      exact WithTop.coe_lt_coe.mpr neg_one_lt_zero
    rw [meromorphicOrderAt_add_eq_left_of_lt hregularA.meromorphicAt hlt,
      hprincipalOrder]
  unfold HasPoleAt
  have ht := tendsto_cobounded_of_meromorphicOrderAt_neg
    (f := R_boundary) (x := x₀)
      (by
        rw [hsumOrder, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) by rfl]
        exact WithTop.coe_lt_coe.mpr neg_one_lt_zero)
  rw [← tendsto_norm_atTop_iff_cobounded] at ht
  simpa [x₀] using ht

/-- Critical-line conclusion (paper §10.1, Theorem 2):
    If `R_∂` is holomorphic on `ℜ x > 0` (and hence has no poles in `ℜ x > 0`),
    and any zero `ρ` with `ℜ ρ > 1/2` would create a pole with residue `m · residue_factor(ρ) ≠ 0`,
    then no zero of `ξ` has `ℜ ρ > 1/2`.

    Combined with the functional equation `ξ(s) = ξ(1 - s)`, all nontrivial zeros satisfy `ℜ ρ = 1/2`. -/
theorem no_zeros_right_of_critical_line
    (h_no_poles : ∀ (x : ℂ), 0 < x.re → ¬ HasPoleAt R_boundary x)
    (rho : ℂ) (hzero : xi rho = 0) (hstrip : 0 < rho.re ∧ rho.re < 1) :
    rho.re ≤ 1 / 2 := by
  by_contra h_gt
  simp only [not_le] at h_gt
  have hx_re : 0 < (rho - 1 / 2).re := by
    simp
    linarith
  have h_pole := R_boundary_hasPoleAt_of_xi_zero rho hzero hstrip
  have h_not_pole := h_no_poles (rho - 1 / 2) hx_re
  exact h_not_pole h_pole

/-- Full Riemann Hypothesis conclusion (paper §10.1):
    Excluding zeros with `ℜ ρ > 1/2` and `ℜ ρ < 1/2` implies `ℜ ρ = 1/2`. -/
theorem riemann_hypothesis_from_pole_exclusion
    (h_right : ∀ (rho : ℂ), xi rho = 0 → 0 < rho.re ∧ rho.re < 1 → rho.re ≤ 1 / 2)
    (rho : ℂ) (hzero : xi rho = 0) (hstrip : 0 < rho.re ∧ rho.re < 1) :
    rho.re = 1 / 2 := by
  have h1 : rho.re ≤ 1 / 2 := h_right rho hzero hstrip
  have h_symm : xi (1 - rho) = 0 := by
    rw [← xi_symmetry]
    exact hzero
  have hstrip_symm : 0 < (1 - rho).re ∧ (1 - rho).re < 1 := by
    simp
    constructor <;> linarith
  have h2 : (1 - rho).re ≤ 1 / 2 := h_right (1 - rho) h_symm hstrip_symm
  simp at h2
  linarith

end
end PoleExclusion
end SEERAVERSE
