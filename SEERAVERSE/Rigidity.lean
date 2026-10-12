import Mathlib
import SEERAVERSE.Setup
import SEERAVERSE.PickInterpolation
import SEERAVERSE.PoleExclusion

/-!
# Nevanlinna-class rigidity and positive-real interpolation (paper Sections 8 & 9)

This module formalizes the analytic rigidity part of the paper.

Important logical separation:
* Step A: interpolation values + Nevanlinna/non-Blaschke uniqueness → identity `R_boundary = H`.
* Step B: identity + holomorphicity of `H` → `R_boundary` has no pole in the right half-plane.

Step B is formalized independently below.
Step A remains a separate theorem obligation.
-/

namespace SEERAVERSE
namespace Rigidity

open Complex
open Filter
open scoped ComplexConjugate

noncomputable section

/-- A complex function `H` is positive-real on a domain `S` if `0 < (H z).re` whenever `z ∈ S`. -/
def IsPositiveRealOn (H : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, 0 < (H z).re

/-- The right half-plane `ℜ z > 0`. -/
def rightHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.re}

/-- The open unit disk `𝔻 = {z | ‖z‖ < 1}`. -/
def openUnitDisk : Set ℂ :=
  {z : ℂ | ‖z‖ < 1}

/-- Standard automorphism of the unit disk sending `a` to `0`. -/
def diskAutomorphism (a z : ℂ) : ℂ :=
  (z - a) / (1 - star a * z)

/-- The norm-square identity underlying invariance of the unit disk. -/
theorem diskAutomorphism_normSq_identity (a z : ℂ) :
    Complex.normSq (1 - star a * z) - Complex.normSq (z - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  rw [Complex.star_def]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    conj_re, conj_im]
  ring

theorem diskAutomorphism_den_ne_zero {a z : ℂ}
    (ha : a ∈ openUnitDisk) (hz : z ∈ openUnitDisk) :
    1 - star a * z ≠ 0 := by
  intro h
  have heq : star a * z = 1 := (sub_eq_zero.mp h).symm
  have hnorm := congrArg norm heq
  simp only [norm_mul, norm_star, norm_one] at hnorm
  have hlt : ‖a‖ * ‖z‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg a) ha (le_of_lt hz)
  linarith

@[simp] theorem diskAutomorphism_self {a : ℂ} (ha : a ∈ openUnitDisk) :
    diskAutomorphism a a = 0 := by
  simp [diskAutomorphism, diskAutomorphism_den_ne_zero ha ha]

theorem diskAutomorphism_ne_zero_of_ne {a z : ℂ}
    (ha : a ∈ openUnitDisk) (hz : z ∈ openUnitDisk) (hza : z ≠ a) :
    diskAutomorphism a z ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr hza) (diskAutomorphism_den_ne_zero ha hz)

/-- A disk automorphism maps the open unit disk to itself. -/
theorem diskAutomorphism_mem_openUnitDisk {a z : ℂ}
    (ha : a ∈ openUnitDisk) (hz : z ∈ openUnitDisk) :
    diskAutomorphism a z ∈ openUnitDisk := by
  have hid := diskAutomorphism_normSq_identity a z
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hid
  have hprod : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    have ha' : ‖a‖ ^ 2 < 1 := by
      simpa using (sq_lt_sq₀ (norm_nonneg a) (by norm_num)).2 ha
    have hz' : ‖z‖ ^ 2 < 1 := by
      simpa using (sq_lt_sq₀ (norm_nonneg z) (by norm_num)).2 hz
    positivity
  have hltSq : ‖z - a‖ ^ 2 < ‖1 - star a * z‖ ^ 2 := by linarith
  have hlt : ‖z - a‖ < ‖1 - star a * z‖ := by nlinarith [norm_nonneg (z - a), norm_nonneg (1 - star a * z)]
  have hden : 0 < ‖1 - star a * z‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  change ‖(z - a) / (1 - star a * z)‖ < 1
  rw [norm_div, div_lt_one hden]
  exact hlt

/-- Two points in the disk cannot make the Pick-kernel denominator vanish. -/
theorem one_sub_mul_star_ne_zero {z u : ℂ}
    (hz : z ∈ openUnitDisk) (hu : u ∈ openUnitDisk) :
    1 - z * star u ≠ 0 := by
  intro h
  have heq : z * star u = 1 := (sub_eq_zero.mp h).symm
  have hnorm := congrArg norm heq
  simp only [norm_mul, norm_star, norm_one] at hnorm
  have hlt : ‖z‖ * ‖u‖ < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg z) hz (le_of_lt hu)
  linarith

/-- The invariant kernel identity for a disk automorphism.  Keeping this
    separate prevents the Schur-reduction proof from expanding both
    automorphisms at once. -/
theorem one_sub_diskAutomorphism_mul_star
    {a z u : ℂ} (ha : a ∈ openUnitDisk)
    (hz : z ∈ openUnitDisk) (hu : u ∈ openUnitDisk) :
    1 - diskAutomorphism a z * star (diskAutomorphism a u) =
      ((1 - a * star a) * (1 - z * star u)) /
        ((1 - star a * z) * (1 - a * star u)) := by
  have hdz := diskAutomorphism_den_ne_zero ha hz
  have hdu := diskAutomorphism_den_ne_zero ha hu
  have hdu' : 1 - a * star u ≠ 0 := one_sub_mul_star_ne_zero ha hu
  have hdz' : 1 - z * star a ≠ 0 := one_sub_mul_star_ne_zero hz ha
  have hstar : star (diskAutomorphism a u) =
      (star u - star a) / (1 - a * star u) := by
    simp [diskAutomorphism, mul_comm]
  rw [hstar]
  simp only [diskAutomorphism]
  field_simp [hdz, hdz', hdu']
  ring

theorem neg_mem_openUnitDisk {a : ℂ} (ha : a ∈ openUnitDisk) :
    -a ∈ openUnitDisk := by
  simpa [openUnitDisk] using ha

/-- `diskAutomorphism (-a)` is the inverse of `diskAutomorphism a`. -/
theorem diskAutomorphism_neg_inverse
    {a u : ℂ} (ha : a ∈ openUnitDisk) (hu : u ∈ openUnitDisk) :
    diskAutomorphism a (diskAutomorphism (-a) u) = u := by
  have hna : -a ∈ openUnitDisk := neg_mem_openUnitDisk ha
  have hv : diskAutomorphism (-a) u ∈ openUnitDisk :=
    diskAutomorphism_mem_openUnitDisk hna hu
  have hinner := diskAutomorphism_den_ne_zero hna hu
  have houter := diskAutomorphism_den_ne_zero ha hv
  have hformula : diskAutomorphism (-a) u = (u + a) / (1 + star a * u) := by
    simp [diskAutomorphism]
  rw [hformula]
  have hinner' : 1 + star a * u ≠ 0 := by simpa using hinner
  have houter' : 1 - star a * ((u + a) / (1 + star a * u)) ≠ 0 := by
    simpa [hformula] using houter
  have hinnerc : 1 + u * star a ≠ 0 := by simpa [mul_comm] using hinner'
  have hnum : (u + a) / (1 + star a * u) - a =
      u * (1 - star a * a) / (1 + star a * u) := by
    field_simp [hinner']
    ring
  have hden : 1 - star a * ((u + a) / (1 + star a * u)) =
      (1 - star a * a) / (1 + star a * u) := by
    field_simp [hinner']
    ring
  have haa : 1 - star a * a ≠ 0 := by
    simpa [mul_comm] using one_sub_mul_star_ne_zero ha ha
  simp only [diskAutomorphism]
  rw [hnum, hden]
  field_simp [hinner', haa]

theorem diskAutomorphism_inverse_neg
    {a z : ℂ} (ha : a ∈ openUnitDisk) (hz : z ∈ openUnitDisk) :
    diskAutomorphism (-a) (diskAutomorphism a z) = z := by
  simpa using diskAutomorphism_neg_inverse (neg_mem_openUnitDisk ha) hz

theorem diskAutomorphism_neg_self
    {a : ℂ} (ha : a ∈ openUnitDisk) :
    diskAutomorphism (-a) 0 = a := by
  simp [diskAutomorphism]

/-- Analyticity of a disk automorphism on the open disk. -/
theorem diskAutomorphism_analyticOnNhd {a : ℂ} (ha : a ∈ openUnitDisk) :
    AnalyticOnNhd ℂ (diskAutomorphism a) openUnitDisk := by
  apply (analyticOnNhd_id.sub analyticOnNhd_const).div
    (analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id))
  intro z hz
  exact diskAutomorphism_den_ne_zero ha hz

/-- The Schur class: analytic maps from `𝔻` to `𝔻`. -/
def schurClass (f : ℂ → ℂ) : Prop :=
  Set.MapsTo f openUnitDisk openUnitDisk ∧ DifferentiableOn ℂ f openUnitDisk

/-- Nevanlinna-Pick interpolation problem data validity on `𝔻`. -/
def NevanlinnaPickProblem {ι : Type*} [Finite ι] (z : ι → ℂ) (w : ι → ℂ) : Prop :=
  (∀ i, z i ∈ openUnitDisk) ∧ (∀ i, w i ∈ openUnitDisk) ∧ Function.Injective z

/-- Solvability of the Nevanlinna-Pick interpolation problem in the Schur class. -/
def HasNevanlinnaPickSolution {ι : Type*} [Finite ι] (z : ι → ℂ) (w : ι → ℂ) : Prop :=
  ∃ f : ℂ → ℂ, schurClass f ∧ ∀ i : ι, f (z i) = w i

/-- Standard Pick kernel on `𝔻`: `(1 - w_i * conj w_j) / (1 - z_i * conj z_j)`. -/
def unitDiskPickKernel {ι : Type*} [Fintype ι] (z w : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => (1 - w i * star (w j)) / (1 - z i * star (z j))

/-- Cayley transform `C(w) = (1 - w) / (1 + w)`. -/
def cayleyTransform (w : ℂ) : ℂ :=
  (1 - w) / (1 + w)

/-- Inverse Cayley transform `C⁻¹(z) = (1 - z) / (1 + z)`. -/
def invCayleyTransform (z : ℂ) : ℂ :=
  (1 - z) / (1 + z)

/-- Cayley map from the right half-plane to the unit disk.  This is the
    normalization used by the Pick nodes, as opposed to `halfPlaneToDisk`,
    which is normalized for the far-right Jensen argument. -/
def rightHalfPlaneToDisk (z : ℂ) : ℂ :=
  (z - 1) / (z + 1)

theorem rightHalfPlaneToDisk_den_ne_zero {z : ℂ} (hz : z ∈ rightHalfPlane) :
    z + 1 ≠ 0 := by
  intro h
  have hz' : z = -1 := by linear_combination h
  rw [hz'] at hz
  norm_num [rightHalfPlane] at hz

theorem rightHalfPlaneToDisk_mem_openUnitDisk {z : ℂ}
    (hz : z ∈ rightHalfPlane) :
    rightHalfPlaneToDisk z ∈ openUnitDisk := by
  have hsq : ‖z - 1‖ ^ 2 < ‖z + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    dsimp [rightHalfPlane] at hz
    nlinarith
  have hden : 0 < ‖z + 1‖ := by
    exact norm_pos_iff.mpr (rightHalfPlaneToDisk_den_ne_zero hz)
  change ‖(z - 1) / (z + 1)‖ < 1
  rw [norm_div, div_lt_one hden]
  nlinarith [norm_nonneg (z - 1), norm_nonneg (z + 1)]

theorem rightHalfPlaneToDisk_analyticOnNhd :
    AnalyticOnNhd ℂ rightHalfPlaneToDisk rightHalfPlane := by
  apply (analyticOnNhd_id.sub analyticOnNhd_const).div
    (analyticOnNhd_id.add analyticOnNhd_const)
  intro z hz
  exact rightHalfPlaneToDisk_den_ne_zero hz

theorem one_add_ne_zero_of_mem_openUnitDisk {w : ℂ}
    (hw : w ∈ openUnitDisk) : 1 + w ≠ 0 := by
  intro h
  have hw' : w = -1 := by linear_combination h
  rw [hw'] at hw
  norm_num [openUnitDisk] at hw

theorem invCayleyTransform_analyticOnNhd :
    AnalyticOnNhd ℂ invCayleyTransform openUnitDisk := by
  apply (analyticOnNhd_const.sub analyticOnNhd_id).div
    (analyticOnNhd_const.add analyticOnNhd_id)
  intro w hw
  exact one_add_ne_zero_of_mem_openUnitDisk hw

theorem invCayleyTransform_re_pos {w : ℂ} (hw : w ∈ openUnitDisk) :
    0 < (invCayleyTransform w).re := by
  have hden : 0 < Complex.normSq (1 + w) := by
    exact Complex.normSq_pos.mpr (one_add_ne_zero_of_mem_openUnitDisk hw)
  rw [invCayleyTransform, Complex.div_re]
  have hnum : ((1 - w).re * (1 + w).re +
      (1 - w).im * (1 + w).im) = 1 - Complex.normSq w := by
    simp [Complex.normSq_apply]
    ring
  rw [← add_div, hnum]
  apply div_pos
  · rw [Complex.normSq_eq_norm_sq]
    have hsq : ‖w‖ ^ 2 < 1 := by
      simpa using (sq_lt_sq₀ (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1)).2 hw
    linarith
  · exact hden

theorem cayleyTransform_mem_openUnitDisk_of_re_pos {z : ℂ}
    (hz : 0 < z.re) : cayleyTransform z ∈ openUnitDisk := by
  have hsq : ‖1 - z‖ ^ 2 < ‖1 + z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hden : 0 < ‖1 + z‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hz' : z = -1 := by linear_combination h
    rw [hz'] at hz
    norm_num at hz
  change ‖(1 - z) / (1 + z)‖ < 1
  rw [norm_div, div_lt_one hden]
  nlinarith [norm_nonneg (1 - z), norm_nonneg (1 + z)]

/-- The Cayley transform is involutive away from `-1`. -/
theorem cayley_involutive (w : ℂ) (hw : w ≠ -1) :
    cayleyTransform (cayleyTransform w) = w := by
  dsimp [cayleyTransform]
  have h1 : 1 + w ≠ 0 := by
    intro h
    have : w = -1 := by linear_combination h
    exact hw this
  have h2 : 1 + (1 - w) / (1 + w) = 2 / (1 + w) := by field_simp; ring
  have h3 : 1 - (1 - w) / (1 + w) = (2 * w) / (1 + w) := by field_simp; ring
  rw [h2, h3]
  field_simp

/-- The far-right half-plane `ℜ z > 4` used for Nevanlinna rigidity (paper §8). -/
def farRightHalfPlane : Set ℂ :=
  {z : ℂ | 4 < z.re}

/-- Difference between the interpolant `H` and the boundary function `R_boundary`. -/
def rigidityDifference (H : ℂ → ℂ) : ℂ → ℂ :=
  fun z => H z - R_boundary z

/-- The rigidity difference vanishes at every Pick interpolation node. -/
theorem rigidityDifference_zero_at_pickNodes
    (H : ℂ → ℂ)
    (h_match : ∀ (i : ℕ),
      H (PickInterpolation.pickNode (i + 1) : ℂ) =
        R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)) :
    ∀ i : ℕ,
      rigidityDifference H (PickInterpolation.pickNode (i + 1) : ℂ) = 0 := by
  intro i
  unfold rigidityDifference
  rw [h_match i]
  ring

/-- Shifted Pick node relative to the boundary `Re z = 4`. -/
def shiftedPickNode (i : ℕ) : ℝ :=
  PickInterpolation.pickNode (i + 1) - 4

/-- Half-plane Blaschke weight of the `i`-th Pick node relative to `H₄`. -/
def pickBlaschkeWeight (i : ℕ) : ℝ :=
  shiftedPickNode i / (1 + (shiftedPickNode i) ^ 2)

/-- Exact formula for the shifted Pick node: `shiftedPickNode i = 2 * i + 1/2`. -/
theorem shiftedPickNode_eq (i : ℕ) :
    shiftedPickNode i = 2 * (i : ℝ) + 1 / 2 := by
  simp [shiftedPickNode, PickInterpolation.pickNode]
  ring

/-- Positivity of the shifted Pick node. -/
theorem shiftedPickNode_pos (i : ℕ) : 0 < shiftedPickNode i := by
  rw [shiftedPickNode_eq]
  positivity

/-- Positivity of the Pick Blaschke weight. -/
theorem pickBlaschkeWeight_pos (i : ℕ) : 0 < pickBlaschkeWeight i := by
  unfold pickBlaschkeWeight
  have hy := shiftedPickNode_pos i
  positivity

/-- Harmonic minorization of the Pick Blaschke weight:
    `1 / (20 * (i + 1)) ≤ pickBlaschkeWeight i`. -/
theorem harmonic_le_pickBlaschkeWeight (i : ℕ) :
    1 / (20 * ((i : ℝ) + 1)) ≤ pickBlaschkeWeight i := by
  rw [pickBlaschkeWeight, shiftedPickNode_eq]
  have hi : 0 ≤ (i : ℝ) := by positivity
  have h1 : 0 < 20 * ((i : ℝ) + 1) := by positivity
  have h2 : 0 < 1 + (2 * (i : ℝ) + 1 / 2) ^ 2 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

/-- Divergence of the harmonic series `∑ 1 / (i + 1) = ∞`. -/
theorem not_summable_harmonic_shift :
    ¬ Summable (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) := by
  intro h
  have hshift :
      Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hall :
      Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) := by
    exact
      (summable_nat_add_iff
        (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 1).mp
        (by simpa using hshift)
  exact Real.not_summable_one_div_natCast hall

/-- Non-Blaschke divergence theorem (paper §8, eq 8.4):
    The Pick lattice points relative to `H₄` satisfy `∑ y_i / (1 + y_i²) = ∞`. -/
theorem pick_lattice_nonBlaschke :
    ¬ Summable pickBlaschkeWeight := by
  intro hsum
  have h_scaled : Summable (fun i : ℕ => 1 / (20 * ((i : ℝ) + 1))) := by
    exact hsum.of_nonneg_of_le (fun i => by positivity) harmonic_le_pickBlaschkeWeight
  have h_harm : Summable (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) := by
    have h_smul := h_scaled.const_smul (20 : ℝ)
    have h_eq : (fun i : ℕ => (20 : ℝ) • (1 / (20 * ((i : ℝ) + 1)))) = (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) := by
      ext i
      have : 0 < 20 * ((i : ℝ) + 1) := by positivity
      simp [smul_eq_mul]
      field_simp
    exact h_eq ▸ h_smul
  exact not_summable_harmonic_shift h_harm

/-- A function is of Nevanlinna class (bounded type) on `S` if it is a quotient of bounded holomorphic functions (paper §9.1, eq 9.4). -/
def IsNevanlinnaOn (f : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∃ (g h : ℂ → ℂ),
    DifferentiableOn ℂ g S ∧
    DifferentiableOn ℂ h S ∧
    (∃ M : ℝ, ∀ z ∈ S, ‖g z‖ ≤ M) ∧
    (∃ M : ℝ, ∀ z ∈ S, ‖h z‖ ≤ M) ∧
    (∀ z ∈ S, h z ≠ 0) ∧
    ∀ z ∈ S, f z = g z / h z

theorem IsNevanlinnaOn.sub {f q : ℂ → ℂ} {S : Set ℂ}
    (hf : IsNevanlinnaOn f S) (hq : IsNevanlinnaOn q S) :
    IsNevanlinnaOn (fun z => f z - q z) S := by
  rcases hf with ⟨gf, hf', hgf, hhf, ⟨Mf, hMf⟩, ⟨Nf, hNf⟩,
    hnf, heqf⟩
  rcases hq with ⟨gq, hq', hgq, hhq, ⟨Mq, hMq⟩, ⟨Nq, hNq⟩,
    hnq, heqq⟩
  refine ⟨fun z => gf z * hq' z - gq z * hf' z,
    fun z => hf' z * hq' z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hgf.mul hhq |>.sub (hgq.mul hhf)
  · exact hhf.mul hhq
  · refine ⟨|Mf| * |Nq| + |Mq| * |Nf|, ?_⟩
    intro z hz
    calc
      ‖gf z * hq' z - gq z * hf' z‖
          ≤ ‖gf z‖ * ‖hq' z‖ + ‖gq z‖ * ‖hf' z‖ := by
            simpa [norm_mul] using norm_sub_le (gf z * hq' z) (gq z * hf' z)
      _ ≤ |Mf| * |Nq| + |Mq| * |Nf| := by
        gcongr
        · exact (hMf z hz).trans (le_abs_self Mf)
        · exact (hNq z hz).trans (le_abs_self Nq)
        · exact (hMq z hz).trans (le_abs_self Mq)
        · exact (hNf z hz).trans (le_abs_self Nf)
  · refine ⟨|Nf| * |Nq|, ?_⟩
    intro z hz
    rw [norm_mul]
    gcongr
    · exact (hNf z hz).trans (le_abs_self Nf)
    · exact (hNq z hz).trans (le_abs_self Nq)
  · intro z hz
    exact mul_ne_zero (hnf z hz) (hnq z hz)
  · intro z hz
    change f z - q z =
      (gf z * hq' z - gq z * hf' z) / (hf' z * hq' z)
    rw [heqf z hz, heqq z hz]
    field_simp [hnf z hz, hnq z hz]

/-- A strict Schur function gives a positive-real (hence bounded-type)
    function by the inverse Cayley transform. -/
theorem invCayley_isNevanlinnaOn {f : ℂ → ℂ} {S : Set ℂ}
    (hfa : DifferentiableOn ℂ f S)
    (hfb : ∀ z ∈ S, ‖f z‖ ≤ 1)
    (hfs : ∀ z ∈ S, ‖f z‖ < 1) :
    IsNevanlinnaOn (fun z => invCayleyTransform (f z)) S := by
  refine ⟨fun z => 1 - f z, fun z => 1 + f z,
    (fun z hz => (differentiableWithinAt_const (1 : ℂ)).sub (hfa z hz)),
    (fun z hz => (differentiableWithinAt_const (1 : ℂ)).add (hfa z hz)),
    ⟨2, ?_⟩, ⟨2, ?_⟩, ?_, ?_⟩
  · intro z hz
    calc
      ‖1 - f z‖ ≤ ‖(1 : ℂ)‖ + ‖f z‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num; linarith [hfb z hz]
  · intro z hz
    calc
      ‖1 + f z‖ ≤ ‖(1 : ℂ)‖ + ‖f z‖ := norm_add_le _ _
      _ ≤ 2 := by norm_num; linarith [hfb z hz]
  · intro z hz hzero
    have : f z = -1 := by linear_combination hzero
    have hlt := hfs z hz
    rw [this] at hlt
    norm_num at hlt
  · intro z hz
    rfl

/-- Cayley map from `Re z > 4` (`farRightHalfPlane`) to the open unit disk `𝔻`. -/
def halfPlaneToDisk (z : ℂ) : ℂ :=
  (z - 5) / (z - 3)

/-- Inverse Cayley map from the open unit disk `𝔻` to `Re z > 4`. -/
def diskToHalfPlane (w : ℂ) : ℂ :=
  4 + (1 + w) / (1 - w)

/-- Inverse Cayley map property: `halfPlaneToDisk (diskToHalfPlane w) = w`. -/
theorem halfPlaneToDisk_diskToHalfPlane (w : ℂ) (hw : w ≠ 1) :
    halfPlaneToDisk (diskToHalfPlane w) = w := by
  unfold halfPlaneToDisk diskToHalfPlane
  have h1 : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h2 : (4 + (1 + w) / (1 - w) - 3) ≠ 0 := by
    have : 4 + (1 + w) / (1 - w) - 3 = 1 + (1 + w) / (1 - w) := by ring
    rw [this]
    have : 1 + (1 + w) / (1 - w) = 2 / (1 - w) := by
      field_simp
      ring
    rw [this]
    exact div_ne_zero (by norm_num) h1
  field_simp
  ring

/-- Cayley map inverse property: `diskToHalfPlane (halfPlaneToDisk z) = z`. -/
theorem diskToHalfPlane_halfPlaneToDisk (z : ℂ) (hz : z ≠ 3) :
    diskToHalfPlane (halfPlaneToDisk z) = z := by
  unfold halfPlaneToDisk diskToHalfPlane
  have h1 : z - 3 ≠ 0 := sub_ne_zero.mpr hz
  have h2 : 1 - (z - 5) / (z - 3) ≠ 0 := by
    have : 1 - (z - 5) / (z - 3) = 2 / (z - 3) := by
      field_simp
      ring
    rw [this]
    exact div_ne_zero (by norm_num) h1
  field_simp
  ring

/-- Pullback of a function on `farRightHalfPlane` to the unit disk `𝔻`. -/
def diskPullback (g : ℂ → ℂ) : ℂ → ℂ :=
  fun w => g (diskToHalfPlane w)

/-- Every Pick node `x_{i+1}` lies in `farRightHalfPlane`. -/
theorem pickNode_in_farRightHalfPlane (i : ℕ) :
    (PickInterpolation.pickNode (i + 1) : ℂ) ∈ farRightHalfPlane := by
  dsimp [farRightHalfPlane, PickInterpolation.pickNode]
  push_cast
  linarith

/-- Pick nodes in the unit disk `𝔻` obtained via Cayley map. -/
def diskPickNode (i : ℕ) : ℂ :=
  halfPlaneToDisk (PickInterpolation.pickNode (i + 1) : ℂ)

/-- Cayley transform used for the finite positive-real Pick problem on the
    full right half-plane.  This is intentionally different from
    `diskPickNode`, which is centered at the boundary `re z = 4` for the
    Jensen argument. -/
def interpolationDiskNode (i : ℕ) : ℂ :=
  ((PickInterpolation.pickNode (i + 1) - 1) /
    (PickInterpolation.pickNode (i + 1) + 1) : ℝ)

/-- Schur-class target value corresponding to the positive-real boundary
    datum at the `i`-th Pick node.  The real part is used because the existing
    matrix `K_boundary_real` contains precisely these real data. -/
def boundaryDiskValue (i : ℕ) : ℂ :=
  cayleyTransform
    ((R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)).re : ℂ)

/-- Reality of the original boundary values at the Pick lattice.  This is
    needed later to identify the real-data interpolant with `R_boundary`. -/
def PickBoundaryValuesReal : Prop :=
  ∀ i : ℕ, (R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)).im = 0

/-- On the half-plane `re s > 1`, the Dirichlet-series formula makes the
    completed zeta function compatible with complex conjugation. -/
theorem completedRiemannZeta_conj_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedZeta_eq_tsum_of_one_lt_re (by simpa using hs),
    completedZeta_eq_tsum_of_one_lt_re hs]
  rw [← zeta_eq_tsum_one_div_nat_cpow (by simpa using hs),
    ← zeta_eq_tsum_one_div_nat_cpow hs, riemannZeta_conj]
  rw [map_mul, map_mul, ← Gamma_conj (s / 2)]
  simp only [map_div₀, Complex.conj_ofNat]
  have hpow : (Real.pi : ℂ) ^ (-conj s / 2) =
      conj ((Real.pi : ℂ) ^ (-s / 2)) := by
    have hpow' := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) (by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
      exact Real.pi_ne_zero.symm)
    simpa only [map_neg, map_div₀, Complex.conj_ofNat, conj_ofReal,
      conj_conj] using hpow'
  rw [hpow]

theorem Lambda_conj_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    Lambda (conj s) = conj (Lambda s) :=
  completedRiemannZeta_conj_of_one_lt_re s hs

theorem xi_conj_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    xi (conj s) = conj (xi s) := by
  simp only [xi, map_mul, map_sub, map_one]
  rw [Lambda_conj_of_one_lt_re s hs]
  simp only [map_div₀, Complex.conj_ofNat, map_one]

/-- The derivative of `Lambda` is real at real points to the right of `1`.
    This follows by differentiating its local conjugation symmetry. -/
theorem deriv_Lambda_real_of_one_lt (x : ℝ) (hx : 1 < x) :
    conj (deriv Lambda (x : ℂ)) = deriv Lambda (x : ℂ) := by
  let U : Set ℂ := {z | 1 < z.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hxU : (x : ℂ) ∈ U := by simpa [U]
  have heq : (conj ∘ Lambda ∘ conj) =ᶠ[nhds (x : ℂ)] Lambda := by
    filter_upwards [hopen.mem_nhds hxU] with z hz
    change conj (Lambda (conj z)) = Lambda z
    rw [Lambda_conj_of_one_lt_re z (by simpa [U] using hz)]
    simp
  have hd := heq.deriv_eq
  rw [deriv_conj_conj] at hd
  simpa using hd

/-- The derivative of `xi` is real at real points to the right of `1`. -/
theorem deriv_xi_real_of_one_lt (x : ℝ) (hx : 1 < x) :
    (deriv xi (x : ℂ)).im = 0 := by
  let U : Set ℂ := {z | 1 < z.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hxU : (x : ℂ) ∈ U := by simpa [U]
  have heq : (conj ∘ xi ∘ conj) =ᶠ[nhds (x : ℂ)] xi := by
    filter_upwards [hopen.mem_nhds hxU] with z hz
    change conj (xi (conj z)) = xi z
    rw [xi_conj_of_one_lt_re z (by simpa [U] using hz)]
    simp
  have hd := heq.deriv_eq
  rw [deriv_conj_conj] at hd
  have hc : conj (deriv xi (x : ℂ)) = deriv xi (x : ℂ) := by simpa using hd
  have him := congrArg Complex.im hc
  simp at him
  linarith

theorem logDeriv_Lambda_real_of_one_lt (x : ℝ) (hx : 1 < x) :
    conj (logDeriv Lambda (x : ℂ)) = logDeriv Lambda (x : ℂ) := by
  simp only [logDeriv_apply, map_div₀]
  rw [deriv_Lambda_real_of_one_lt x hx]
  have hval : conj (Lambda (x : ℂ)) = Lambda (x : ℂ) := by
    simpa using (Lambda_conj_of_one_lt_re (x : ℂ) (by simpa using hx)).symm
  rw [hval]

theorem logDeriv_xi_real_of_one_lt (x : ℝ) (hx : 1 < x) :
    conj (logDeriv xi (x : ℂ)) = logDeriv xi (x : ℂ) := by
  simp only [logDeriv_apply, map_div₀]
  have hderiv : conj (deriv xi (x : ℂ)) = deriv xi (x : ℂ) := by
    apply Complex.ext
    · simp
    · simp [deriv_xi_real_of_one_lt x hx]
  rw [hderiv]
  have hval : conj (xi (x : ℂ)) = xi (x : ℂ) := by
    simpa using (xi_conj_of_one_lt_re (x : ℂ) (by simpa using hx)).symm
  rw [hval]

theorem kappa_conj : conj kappa = kappa := by
  have hA : conj A = A := by
    rw [A_eq_logDeriv_Lambda_3]
    exact logDeriv_Lambda_real_of_one_lt 3 (by norm_num)
  simp only [kappa, map_add, map_mul, map_div₀, map_ofNat, map_one, hA]

/-- `R_boundary` is real on the real ray whose centered coordinate lies to
    the right of `1`.  This is the precise local fact needed by the Pick data. -/
theorem R_boundary_real_of_one_lt_centered (x : ℝ) (hx : 1 < 1 / 2 + x) :
    (R_boundary (x : ℂ)).im = 0 := by
  have hlog := logDeriv_xi_real_of_one_lt (1 / 2 + x) hx
  have hc : conj (R_boundary (x : ℂ)) = R_boundary (x : ℂ) := by
    simp only [R_boundary, map_div₀, map_sub, map_mul, map_add, map_ofNat,
      conj_ofReal]
    norm_num at hlog ⊢
    rw [hlog, kappa_conj]
  have him := congrArg Complex.im hc
  simp at him
  linarith

/-- The SEERAVERSE boundary values at every Pick node are real. -/
theorem pickBoundaryValues_real : PickBoundaryValuesReal := by
  intro i
  apply R_boundary_real_of_one_lt_centered
  norm_num [PickInterpolation.pickNode]
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

theorem pickBoundaryValue_eq_realCast (i : ℕ) :
    R_boundary (PickInterpolation.pickNode (i + 1) : ℂ) =
      ((R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using pickBoundaryValues_real i

theorem boundaryDiskValue_real (i : ℕ) : (boundaryDiskValue i).im = 0 := by
  simp [boundaryDiskValue, cayleyTransform, Complex.div_im]

/-- Because the boundary datum is real, the disk datum defined from its real
    part is exactly the Cayley transform of the original complex value. -/
theorem boundaryDiskValue_eq_cayley_R_boundary (i : ℕ) :
    boundaryDiskValue i =
      cayleyTransform (R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)) := by
  unfold boundaryDiskValue
  rw [← pickBoundaryValue_eq_realCast i]

/-- Existence of one analytic Schur-bounded solution for the first `N`
    transformed Pick data.  The implication from positivity of the finite
    Pick matrix to this proposition is a currently separate obligation. -/
def HasFiniteSchurInterpolant (N : ℕ) : Prop :=
  ∃ f : ℂ → ℂ,
    AnalyticOnNhd ℂ f openUnitDisk ∧
    (∀ z ∈ openUnitDisk, ‖f z‖ ≤ 1) ∧
    ∀ i : ℕ, i < N → f (interpolationDiskNode i) = boundaryDiskValue i

/-- The classical disk Pick matrix for the first `N` Cayley-transformed
    boundary interpolation data. -/
def diskPickMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  unitDiskPickKernel
    (fun i => interpolationDiskNode i.val)
    (fun i => boundaryDiskValue i.val)

/-- Real boundary datum used by `K_boundary_real`. -/
def pickBoundaryRealValue (i : ℕ) : ℝ :=
  (R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)).re

/-- Diagonal congruence factor between the right-half-plane and disk Pick
    kernels. -/
def pickScale {N : ℕ} (i : Fin N) : ℂ :=
  (((PickInterpolation.pickNode (i.val + 1) + 1) /
    (pickBoundaryRealValue i.val + 1) : ℝ) : ℂ)

/-- Entry formula for the real positive-real Pick matrix. -/
theorem K_boundary_real_entry (N : ℕ) (i j : Fin N) :
    PickInterpolation.K_boundary_real N i j =
      (pickBoundaryRealValue i.val + pickBoundaryRealValue j.val) /
        (PickInterpolation.pickNode (i.val + 1) +
          PickInterpolation.pickNode (j.val + 1)) := by
  simp [PickInterpolation.K_boundary_real, PickInterpolation.K_boundary,
    PickInterpolation.pickKernel, PickInterpolation.w, pickBoundaryRealValue,
    Complex.div_re, Complex.normSq]
  field_simp

/-- Positive definiteness forces every real Pick datum to be positive. -/
theorem pickBoundaryRealValue_pos {N : ℕ}
    (hpos : Matrix.PosDef
      (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ))
    (i : Fin N) :
    0 < pickBoundaryRealValue i.val := by
  have hdiag := hpos.diag_pos (i := i)
  rw [K_boundary_real_entry N i i] at hdiag
  have hx : 0 < PickInterpolation.pickNode (i.val + 1) := by
    simp [PickInterpolation.pickNode]
    positivity
  have hden : 0 <
      PickInterpolation.pickNode (i.val + 1) +
        PickInterpolation.pickNode (i.val + 1) := add_pos hx hx
  rw [div_pos_iff] at hdiag
  rcases hdiag with h | h
  · linarith
  · linarith

/-- Exact entrywise Cayley identity.  The finite interpolation Cayley map is
    based at the boundary `re z = 0`, so its node is `(x - 1) / (x + 1)`. -/
theorem cayley_pick_entry_identity {N : ℕ}
    (hpos : Matrix.PosDef
      (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ))
    (i j : Fin N) :
    diskPickMatrix N i j =
      star (pickScale i) *
        ((PickInterpolation.K_boundary_real N i j : ℝ) : ℂ) *
      pickScale j := by
  have hi := pickBoundaryRealValue_pos hpos i
  have hj := pickBoundaryRealValue_pos hpos j
  have hxi : 0 < PickInterpolation.pickNode (i.val + 1) + 1 := by
    simp [PickInterpolation.pickNode]
    positivity
  have hxj : 0 < PickInterpolation.pickNode (j.val + 1) + 1 := by
    simp [PickInterpolation.pickNode]
    positivity
  let xi := PickInterpolation.pickNode (i.val + 1)
  let xj := PickInterpolation.pickNode (j.val + 1)
  let ai := pickBoundaryRealValue i.val
  let aj := pickBoundaryRealValue j.val
  have hreal :
      (1 - ((1 - ai) / (1 + ai)) * ((1 - aj) / (1 + aj))) /
          (1 - ((xi - 1) / (xi + 1)) * ((xj - 1) / (xj + 1))) =
        ((xi + 1) / (ai + 1)) * ((ai + aj) / (xi + xj)) *
          ((xj + 1) / (aj + 1)) := by
    have hai : ai + 1 ≠ 0 := by dsimp [ai]; linarith
    have haj : aj + 1 ≠ 0 := by dsimp [aj]; linarith
    have hpair : (1 + ai) * (1 + aj) ≠ 0 := by
      apply mul_ne_zero <;> linarith
    have hxis : xi + 1 ≠ 0 := by exact hxi.ne'
    have hxjs : xj + 1 ≠ 0 := by exact hxj.ne'
    have hsum_pos : 0 < xi + xj := by
      dsimp [xi, xj]
      simp [PickInterpolation.pickNode]
      positivity
    have hsum : xi + xj ≠ 0 := hsum_pos.ne'
    have hprod : 1 + ai + ai * aj + aj ≠ 0 := by
      have hai_pos : 0 < ai := by exact hi
      have haj_pos : 0 < aj := by exact hj
      nlinarith [mul_pos hai_pos haj_pos]
    have htwosum : xi * 2 + xj * 2 ≠ 0 := by
      nlinarith
    have hvalue :
        1 - ((1 - ai) / (1 + ai)) * ((1 - aj) / (1 + aj)) =
          2 * (ai + aj) / ((1 + ai) * (1 + aj)) := by
      field_simp [hai, haj]
      rw [sub_eq_iff_eq_add, ← add_div]
      rw [eq_div_iff hpair]
      ring
    have hnode :
        1 - ((xi - 1) / (xi + 1)) * ((xj - 1) / (xj + 1)) =
          2 * (xi + xj) / ((xi + 1) * (xj + 1)) := by
      field_simp [hxis, hxjs]
      ring
    rw [hvalue, hnode]
    field_simp [hai, haj, hxis, hxjs, hsum]
    rw [div_eq_iff hpair]
    ring
  rw [K_boundary_real_entry N i j]
  simpa [diskPickMatrix, unitDiskPickKernel, boundaryDiskValue,
    interpolationDiskNode, cayleyTransform, pickScale, pickBoundaryRealValue,
    xi, xj, ai, aj] using
    congrArg (fun r : ℝ => (r : ℂ)) hreal

/-- Matrix form of `cayley_pick_entry_identity`: the disk Pick matrix is a
    diagonal congruence of the complexification of `K_boundary_real`. -/
theorem cayley_pick_matrix_eq_conj_diagonal {N : ℕ}
    (hpos : Matrix.PosDef
      (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    diskPickMatrix N =
      Matrix.diagonal (fun i => star (pickScale i)) *
        (PickInterpolation.K_boundary_real N).map Complex.ofRealHom *
      Matrix.diagonal pickScale := by
  classical
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact cayley_pick_entry_identity hpos i j

/-- Positive semidefiniteness for a complex Hermitian matrix, expressed via
    the real part of its Hermitian quadratic form. -/
def IsComplexPosSemidef {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) : Prop :=
  M.IsHermitian ∧
    ∀ x : n → ℂ, 0 ≤ (dotProduct (star x) (M.mulVec x)).re

/-- Vector supported at two coordinates, used to probe a Hermitian quadratic
    form without an epsilon or discriminant argument. -/
def twoPointVector {n : Type*} [DecidableEq n]
    (k j : n) (c : ℂ) : n → ℂ :=
  Pi.single k 1 + Pi.single j c

/-- Expansion of a quadratic form on `e_k + c e_j`. -/
theorem quadraticForm_twoPoint {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (k j : n) (c : ℂ) :
    dotProduct (star (twoPointVector k j c))
        (A.mulVec (twoPointVector k j c)) =
      A k k + A k j * c + star c * A j k + star c * A j j * c := by
  classical
  simp [twoPointVector, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    Matrix.mulVec_single, single_dotProduct, mul_add, add_mul]
  ring

theorem complexPSD_diagonal_re_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : IsComplexPosSemidef A) (j : n) :
    0 ≤ (A j j).re := by
  have hq := hA.2 (twoPointVector j j 0)
  rw [quadraticForm_twoPoint A j j 0] at hq
  simpa using hq

theorem pick_psd_target_norm_le_one
    {N : ℕ} {z w : Fin N → ℂ}
    (hz : ∀ i, z i ∈ openUnitDisk)
    (hP : IsComplexPosSemidef (unitDiskPickKernel z w)) (k : Fin N) :
    ‖w k‖ ≤ 1 := by
  have hdiag := complexPSD_diagonal_re_nonneg hP k
  have hden : 0 < 1 - ‖z k‖ ^ 2 := by
    have hsq : ‖z k‖ ^ 2 < 1 := by
      simpa using (sq_lt_sq₀ (norm_nonneg (z k)) (by norm_num)).2 (hz k)
    linarith
  have heq : (unitDiskPickKernel z w k k).re =
      (1 - ‖w k‖ ^ 2) / (1 - ‖z k‖ ^ 2) := by
    simp [unitDiskPickKernel, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    norm_cast
  rw [heq] at hdiag
  have hnum : 0 ≤ 1 - ‖w k‖ ^ 2 := by
    rcases (div_nonneg_iff.mp hdiag) with h | h
    · exact h.1
    · linarith
  nlinarith [norm_nonneg (w k)]

/-- For a complex Hermitian positive-semidefinite matrix, a zero diagonal
    entry forces its entire row to vanish. -/
theorem complexPSD_row_eq_zero_of_diagonal_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : IsComplexPosSemidef A)
    {k : n} (hkk : A k k = 0) :
    ∀ j, A k j = 0 := by
  intro j
  by_cases hjk : j = k
  · subst j
    exact hkk
  let a : ℂ := A k j
  let d : ℝ := (A j j).re
  have hd : 0 ≤ d := by
    exact complexPSD_diagonal_re_nonneg hA j
  have hd1 : 0 < d + 1 := by linarith
  let c : ℂ := -(star a) / (d + 1)
  have hjkA : A j k = star a := by
    dsimp [a]
    exact (hA.1.apply j k).symm
  have hjj : A j j = (d : ℂ) := by
    exact (hA.1.coe_re_apply_self j).symm
  have hq := hA.2 (twoPointVector k j c)
  rw [quadraticForm_twoPoint A k j c, hkk, hjkA, hjj] at hq
  have hcstar : star c = -a / (d + 1) := by
    dsimp [c]
    simp only [starRingEnd_apply, star_div₀, star_neg, star_star,
      star_add, star_one]
    rw [show star (d : ℂ) = (d : ℂ) by rw [Complex.star_def, conj_ofReal]]
  have hformula :
      (0 + a * c + star c * star a + star c * (d : ℂ) * c).re =
        -(Complex.normSq a * (d + 2)) / (d + 1) ^ 2 := by
    have heq :
        0 + a * c + star c * star a + star c * (d : ℂ) * c =
          ((-(Complex.normSq a * (d + 2)) / (d + 1) ^ 2 : ℝ) : ℂ) := by
      rw [hcstar]
      dsimp [c]
      have hcast :
          ((-(Complex.normSq a * (d + 2)) / (d + 1) ^ 2 : ℝ) : ℂ) =
            -(Complex.normSq a : ℂ) * ((d : ℂ) + 2) /
              (((d : ℂ) + 1) ^ 2) := by
        norm_cast
        ring
      rw [hcast]
      have hnormSq : ((Complex.normSq a : ℝ) : ℂ) = a * star a := by
        rw [Complex.star_def, Complex.mul_conj]
      rw [hnormSq]
      have hdne : ((d : ℂ) + 1) ≠ 0 := by
        exact_mod_cast (ne_of_gt hd1)
      field_simp [hdne]
      simp only [starRingEnd_apply]
      ring
    exact congrArg Complex.re heq
  rw [hformula] at hq
  by_contra ha
  have hnormSq : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  have hnum : 0 < Complex.normSq a * (d + 2) := by positivity
  have hden : 0 < (d + 1) ^ 2 := sq_pos_of_pos hd1
  have hneg : -(Complex.normSq a * (d + 2)) / (d + 1) ^ 2 < 0 := by
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hnum) hden
  linarith

/-- Once a boundary target has a zero row in its Pick matrix, all targets are
    forced to be that same boundary value.  The remaining PSD task is exactly
    to derive the zero-row hypothesis from the zero diagonal pivot. -/
theorem pick_boundary_value_forces_constant_data_of_row_zero
    {ι : Type*} [Fintype ι] (z w : ι → ℂ) (k : ι)
    (hz : ∀ i, z i ∈ openUnitDisk)
    (hwk : ‖w k‖ = 1)
    (hrow : ∀ j, unitDiskPickKernel z w k j = 0) :
    ∀ j, w j = w k := by
  intro j
  have hden : 1 - z k * star (z j) ≠ 0 :=
    one_sub_mul_star_ne_zero (hz k) (hz j)
  have hnum : 1 - w k * star (w j) = 0 := by
    have h := hrow j
    simp only [unitDiskPickKernel] at h
    exact (div_eq_zero_iff.mp h).resolve_right hden
  have hwk0 : w k ≠ 0 := by
    intro hk
    simp [hk] at hwk
  have hprod : w k * star (w j) = 1 := (sub_eq_zero.mp hnum).symm
  have hself : w k * star (w k) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hwk]
    norm_num
  have hstar : star (w j) = star (w k) := by
    apply mul_left_cancel₀ hwk0
    rw [hprod, hself]
  exact star_injective hstar

theorem pick_boundary_value_diagonal_zero
    {ι : Type*} [Fintype ι] (z w : ι → ℂ) (k : ι)
    (hz : z k ∈ openUnitDisk) (hwk : ‖w k‖ = 1) :
    unitDiskPickKernel z w k k = 0 := by
  have hden : 1 - z k * star (z k) ≠ 0 :=
    one_sub_mul_star_ne_zero hz hz
  rw [unitDiskPickKernel, div_eq_zero_iff]
  left
  rw [sub_eq_zero]
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hwk]
  norm_num

/-- A real positive-semidefinite matrix remains positive semidefinite after
    scalar extension to `ℂ`, in the explicit quadratic-form sense used here. -/
theorem isComplexPosSemidef_map_ofReal {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    IsComplexPosSemidef (A.map Complex.ofRealHom) := by
  constructor
  · have hHerm := hA.1
    unfold Matrix.IsHermitian at hHerm ⊢
    ext i j
    have hij := congr_fun (congr_fun hHerm i) j
    simpa [Matrix.conjTranspose_apply] using
      congrArg (fun r : ℝ => (r : ℂ)) hij
  · intro x
    have hre := hA.dotProduct_mulVec_nonneg (fun i => (x i).re)
    have him := hA.dotProduct_mulVec_nonneg (fun i => (x i).im)
    rw [show
      (dotProduct (star x) ((A.map Complex.ofRealHom).mulVec x)).re =
        dotProduct (fun i => (x i).re) (A.mulVec fun i => (x i).re) +
        dotProduct (fun i => (x i).im) (A.mulVec fun i => (x i).im) by
          simp [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.mul_re]
          simp only [Finset.sum_add_distrib]]
    exact add_nonneg hre him

/-- Complex positive semidefiniteness is preserved by `Bᴴ * A * B`. -/
theorem IsComplexPosSemidef.conjTranspose_mul_mul_same
    {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m m ℂ} (hA : IsComplexPosSemidef A)
    (B : Matrix m n ℂ) :
    IsComplexPosSemidef (Matrix.conjTranspose B * A * B) := by
  constructor
  · exact Matrix.isHermitian_conjTranspose_mul_mul B hA.1
  · intro x
    simpa only [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul] using hA.2 (B.mulVec x)

/-- Nonnegative real scalar multiplication preserves complex PSD. -/
theorem IsComplexPosSemidef.nonneg_real_smul
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsComplexPosSemidef A) {c : ℝ} (hc : 0 ≤ c) :
    IsComplexPosSemidef ((c : ℂ) • A) := by
  let B : Matrix n n ℂ := Matrix.diagonal (fun _ => (Real.sqrt c : ℂ))
  have hcongr := hA.conjTranspose_mul_mul_same B
  convert hcongr using 1
  ext i j
  have hs : (c : ℂ) = (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) := by
    norm_cast
    exact (Real.mul_self_sqrt hc).symm
  simp [B]
  rw [hs]
  ac_rfl

/-- Column embedding whose range is the graph used to evaluate a pivot Schur
    complement as a restriction of the original quadratic form. -/
def schurEmbedding {N : ℕ} (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Matrix (Fin (N + 1)) (Fin N) ℂ :=
  fun r j => Fin.cases (-(P 0 0)⁻¹ * P 0 j.succ)
    (fun i => if i = j then 1 else 0) r

theorem mul_schurEmbedding_apply
    {N : ℕ} (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (r : Fin (N + 1)) (j : Fin N) :
    (P * schurEmbedding P) r j =
      P r j.succ - P r 0 * (P 0 0)⁻¹ * P 0 j.succ := by
  classical
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [schurEmbedding]
  ring

theorem schurEmbedding_congruence_apply
    {N : ℕ} (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hp : P 0 0 ≠ 0) (i j : Fin N) :
    (Matrix.conjTranspose (schurEmbedding P) * P * schurEmbedding P) i j =
      P i.succ j.succ - P i.succ 0 * (P 0 0)⁻¹ * P 0 j.succ := by
  classical
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
  simp [Matrix.conjTranspose_apply, schurEmbedding,
    mul_schurEmbedding_apply, hp]

/-- A nonzero scalar pivot has a PSD Schur complement.  Positivity follows by
    restricting the original quadratic form to `schurEmbedding P`. -/
theorem complexPSD_schurComplement
    {N : ℕ} {P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hP : IsComplexPosSemidef P) (hp : P 0 0 ≠ 0) :
    IsComplexPosSemidef (fun i j : Fin N =>
      P i.succ j.succ - P i.succ 0 * (P 0 0)⁻¹ * P 0 j.succ) := by
  have hcongr := hP.conjTranspose_mul_mul_same (schurEmbedding P)
  have heq : (fun i j : Fin N =>
      P i.succ j.succ - P i.succ 0 * (P 0 0)⁻¹ * P 0 j.succ) =
      Matrix.conjTranspose (schurEmbedding P) * P * schurEmbedding P := by
    ext i j
    exact (schurEmbedding_congruence_apply P hp i j).symm
  rw [heq]
  exact hcongr

/-- Algebraic compatibility required between the positive-real half-plane
    Pick matrix used in `PickInterpolation` and the classical disk matrix. -/
def CayleyPickMatrixCompatibility : Prop :=
  ∀ N : ℕ,
    Matrix.PosDef
      (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ) →
    IsComplexPosSemidef (diskPickMatrix N)

/-- The Cayley congruence transports strict positivity of the real
    half-plane Pick matrix to positive semidefiniteness of the disk matrix. -/
theorem cayleyPickMatrixCompatibility_proved :
    CayleyPickMatrixCompatibility := by
  intro N hpos
  rw [cayley_pick_matrix_eq_conj_diagonal hpos]
  have hbase := isComplexPosSemidef_map_ofReal hpos.posSemidef
  have hcongr := hbase.conjTranspose_mul_mul_same
    (Matrix.diagonal (fun i : Fin N => pickScale i))
  convert hcongr using 1 <;> ext i j <;> simp

/-- The finite Nevanlinna--Pick criterion in the exact disk normalization
    used by this module. -/
def FiniteNevanlinnaPickCriterion : Prop :=
  ∀ N : ℕ,
    IsComplexPosSemidef (diskPickMatrix N) ↔ HasFiniteSchurInterpolant N

/-- Necessity half of the finite Pick theorem for the concrete boundary data. -/
def FiniteNevanlinnaPickNecessity : Prop :=
  ∀ N : ℕ, HasFiniteSchurInterpolant N →
    IsComplexPosSemidef (diskPickMatrix N)

/-- Sufficiency half of the finite Pick theorem for the concrete boundary data. -/
def FiniteNevanlinnaPickSufficiency : Prop :=
  ∀ N : ℕ, IsComplexPosSemidef (diskPickMatrix N) →
    HasFiniteSchurInterpolant N

/-- Splitting the finite Pick criterion keeps kernel positivity and the Schur
    algorithm as separately auditable obligations. -/
theorem finiteNevanlinnaPickCriterion_iff_halves :
    FiniteNevanlinnaPickCriterion ↔
      FiniteNevanlinnaPickNecessity ∧ FiniteNevanlinnaPickSufficiency := by
  constructor
  · intro h
    exact ⟨fun N => (h N).2, fun N => (h N).1⟩
  · rintro ⟨hne, hsu⟩ N
    exact ⟨hsu N, hne N⟩

/-- Closed-Schur version of a finite disk interpolation problem.  This is the
    exact conclusion stable under the later normal-family limit. -/
def HasClosedSchurSolution {ι : Type*} [Finite ι]
    (z w : ι → ℂ) : Prop :=
  ∃ f : ℂ → ℂ,
    AnalyticOnNhd ℂ f openUnitDisk ∧
    (∀ u ∈ openUnitDisk, ‖f u‖ ≤ 1) ∧
    ∀ i, f (z i) = w i

/-- Inverse one-step Schur reconstruction. -/
def inverseSchurReconstruction (z₀ w₀ : ℂ) (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => diskAutomorphism (-w₀)
    (diskAutomorphism z₀ z * g (diskAutomorphism z₀ z))

theorem inverseSchur_inner_mem_openUnitDisk
    {z₀ : ℂ} (hz₀ : z₀ ∈ openUnitDisk) {g : ℂ → ℂ}
    (hg : ∀ z ∈ openUnitDisk, ‖g z‖ ≤ 1) :
    ∀ z ∈ openUnitDisk,
      diskAutomorphism z₀ z * g (diskAutomorphism z₀ z) ∈ openUnitDisk := by
  intro z hz
  change ‖diskAutomorphism z₀ z * g (diskAutomorphism z₀ z)‖ < 1
  rw [norm_mul]
  have hphi := diskAutomorphism_mem_openUnitDisk hz₀ hz
  exact mul_lt_one_of_nonneg_of_lt_one_left
    (norm_nonneg (diskAutomorphism z₀ z))
    hphi (hg _ hphi)

theorem inverseSchurReconstruction_analyticOnNhd
    {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ openUnitDisk) (hw₀ : w₀ ∈ openUnitDisk)
    {g : ℂ → ℂ} (hga : AnalyticOnNhd ℂ g openUnitDisk)
    (hgb : ∀ z ∈ openUnitDisk, ‖g z‖ ≤ 1) :
    AnalyticOnNhd ℂ (inverseSchurReconstruction z₀ w₀ g) openUnitDisk := by
  have hphi := diskAutomorphism_analyticOnNhd hz₀
  have hphimap : Set.MapsTo (diskAutomorphism z₀) openUnitDisk openUnitDisk :=
    fun _ hz => diskAutomorphism_mem_openUnitDisk hz₀ hz
  have hgcomp := hga.comp hphi hphimap
  have hinner := hphi.mul hgcomp
  have hmap := inverseSchur_inner_mem_openUnitDisk hz₀ hgb
  change AnalyticOnNhd ℂ
    (fun z => diskAutomorphism (-w₀)
      (diskAutomorphism z₀ z * g (diskAutomorphism z₀ z))) openUnitDisk
  simpa [Function.comp_def] using
    (diskAutomorphism_analyticOnNhd (neg_mem_openUnitDisk hw₀)).comp hinner hmap

theorem inverseSchurReconstruction_bound
    {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ openUnitDisk) (hw₀ : w₀ ∈ openUnitDisk)
    {g : ℂ → ℂ} (hgb : ∀ z ∈ openUnitDisk, ‖g z‖ ≤ 1) :
    ∀ z ∈ openUnitDisk, ‖inverseSchurReconstruction z₀ w₀ g z‖ ≤ 1 := by
  intro z hz
  exact le_of_lt (diskAutomorphism_mem_openUnitDisk (neg_mem_openUnitDisk hw₀)
    (inverseSchur_inner_mem_openUnitDisk hz₀ hgb z hz))

theorem inverseSchurReconstruction_pivot
    {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ openUnitDisk) (hw₀ : w₀ ∈ openUnitDisk)
    (g : ℂ → ℂ) : inverseSchurReconstruction z₀ w₀ g z₀ = w₀ := by
  simp [inverseSchurReconstruction, diskAutomorphism_self hz₀,
    diskAutomorphism_neg_self hw₀]

/-- Constant target data of norm at most one have the constant closed-Schur
    interpolant, including the boundary case of norm exactly one. -/
theorem hasClosedSchurSolution_of_constant_data
    {ι : Type*} [Finite ι] (z w : ι → ℂ) (k : ι)
    (hw : ‖w k‖ ≤ 1) (hconst : ∀ i, w i = w k) :
    HasClosedSchurSolution z w := by
  refine ⟨fun _ => w k, analyticOnNhd_const, ?_, ?_⟩
  · intro u hu
    exact hw
  · intro i
    exact (hconst i).symm

/-- The complete PSD-side boundary branch of finite Nevanlinna--Pick: an
    interior node with a unimodular target forces constant target data and
    hence admits the constant closed-Schur interpolant. -/
theorem pick_psd_boundary_value_forces_constant_data
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z w : ι → ℂ) (k : ι)
    (hz : ∀ i, z i ∈ openUnitDisk)
    (hP : IsComplexPosSemidef (unitDiskPickKernel z w))
    (hwk : ‖w k‖ = 1) :
    ∀ j, w j = w k := by
  apply pick_boundary_value_forces_constant_data_of_row_zero z w k hz hwk
  exact complexPSD_row_eq_zero_of_diagonal_eq_zero hP
    (pick_boundary_value_diagonal_zero z w k (hz k) hwk)

theorem hasClosedSchurSolution_of_pick_psd_boundary_value
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z w : ι → ℂ) (k : ι)
    (hz : ∀ i, z i ∈ openUnitDisk)
    (hP : IsComplexPosSemidef (unitDiskPickKernel z w))
    (hwk : ‖w k‖ = 1) :
    HasClosedSchurSolution z w := by
  apply hasClosedSchurSolution_of_constant_data z w k (le_of_eq hwk)
  exact pick_psd_boundary_value_forces_constant_data z w k hz hP hwk

/-- General finite Nevanlinna--Pick statement in the closed-Schur
    normalization actually consumed by the Montel construction. -/
def GeneralFiniteNevanlinnaPickCriterion : Prop :=
  ∀ {ι : Type} [Fintype ι] (z w : ι → ℂ),
    Function.Injective z →
    (∀ i, z i ∈ openUnitDisk) →
    (IsComplexPosSemidef (unitDiskPickKernel z w) ↔
      HasClosedSchurSolution z w)

/-! ### The nondegenerate Schur reduction -/

/-- Nodes obtained after moving the pivot node to zero. -/
def reducedPickNode {N : ℕ} (z : Fin (N + 1) → ℂ) (i : Fin N) : ℂ :=
  diskAutomorphism (z 0) (z i.succ)

/-- Targets for the one-step Schur reduction.  The denominator is nonzero
    when the original nodes are distinct. -/
def reducedPickValue {N : ℕ} (z w : Fin (N + 1) → ℂ) (i : Fin N) : ℂ :=
  diskAutomorphism (w 0) (w i.succ) / reducedPickNode z i

/-- The scalar appearing on the right of the diagonal congruence between the
    reduced Pick matrix and the pivot Schur complement. -/
def pickReductionScale {N : ℕ} (z w : Fin (N + 1) → ℂ) (i : Fin N) : ℂ :=
  (1 - z 0 * star (z i.succ)) ^ 2 /
    ((star (z i.succ) - star (z 0)) * (1 - w 0 * star (w i.succ)))

/-- Entrywise Schur complement of the pivot `(0,0)` in the original Pick
    matrix. -/
def pickSchurComplementEntry {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (i j : Fin N) : ℂ :=
  unitDiskPickKernel z w i.succ j.succ -
    unitDiskPickKernel z w i.succ 0 *
      (unitDiskPickKernel z w 0 0)⁻¹ *
        unitDiskPickKernel z w 0 j.succ

theorem reduced_den_node_ne_zero
    {N : ℕ} (z : Fin (N + 1) → ℂ) (hz : ∀ i, z i ∈ openUnitDisk)
    (hinj : Function.Injective z) (i : Fin N) :
    reducedPickNode z i ≠ 0 := by
  apply diskAutomorphism_ne_zero_of_ne (hz 0) (hz i.succ)
  exact hinj.ne (Fin.succ_ne_zero i)

theorem reduced_den_value_ne_zero
    {N : ℕ} (w : Fin (N + 1) → ℂ) (hw : ∀ i, w i ∈ openUnitDisk)
    (i : Fin N) : 1 - star (w 0) * w i.succ ≠ 0 :=
  diskAutomorphism_den_ne_zero (hw 0) (hw i.succ)

theorem pickReductionScale_den_ne_zero
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (hinj : Function.Injective z) (i : Fin N) :
    (star (z i.succ) - star (z 0)) * (1 - w 0 * star (w i.succ)) ≠ 0 := by
  apply mul_ne_zero
  · simpa [star_sub] using star_ne_zero.mpr
      (sub_ne_zero.mpr (hinj.ne (Fin.succ_ne_zero i)))
  · exact one_sub_mul_star_ne_zero (hw 0) (hw i.succ)

theorem pick_pivot_ne_zero
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : z 0 ∈ openUnitDisk) (hw : w 0 ∈ openUnitDisk) :
    unitDiskPickKernel z w 0 0 ≠ 0 := by
  exact div_ne_zero (one_sub_mul_star_ne_zero hw hw)
    (one_sub_mul_star_ne_zero hz hz)

/-- The elementary numerator cancellation used in the Pick Schur
    complement.  Notice the order in the second factor: the opposite order
    would give the negative of this expression. -/
theorem pick_numerator_difference_identity (a b c : ℂ) :
    (1 - a * star b) * (1 - c * star c) -
        (1 - a * star c) * (1 - c * star b) =
      (a - c) * (star c - star b) := by
  ring

/-- A common-denominator form of the pivot Schur complement.  All subsequent
    factorization lemmas operate only on its numerator. -/
theorem pickSchurComplementEntry_commonDen_formula
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (i j : Fin N) :
    pickSchurComplementEntry z w i j =
      ((1 - w i.succ * star (w j.succ)) *
            (1 - z i.succ * star (z 0)) *
            (1 - z 0 * star (z j.succ)) *
            (1 - w 0 * star (w 0)) -
          (1 - w i.succ * star (w 0)) *
            (1 - w 0 * star (w j.succ)) *
            (1 - z i.succ * star (z j.succ)) *
            (1 - z 0 * star (z 0))) /
        ((1 - z i.succ * star (z j.succ)) *
          (1 - z i.succ * star (z 0)) *
          (1 - z 0 * star (z j.succ)) *
          (1 - w 0 * star (w 0))) := by
  have hz00 := one_sub_mul_star_ne_zero (hz 0) (hz 0)
  have hw00 := one_sub_mul_star_ne_zero (hw 0) (hw 0)
  have hzij := one_sub_mul_star_ne_zero (hz i.succ) (hz j.succ)
  have hzi0 := one_sub_mul_star_ne_zero (hz i.succ) (hz 0)
  have hz0j := one_sub_mul_star_ne_zero (hz 0) (hz j.succ)
  have hz00c : 1 - star (z 0) * z 0 ≠ 0 := by simpa [mul_comm] using hz00
  have hzijc : 1 - star (z j.succ) * z i.succ ≠ 0 := by
    simpa [mul_comm] using hzij
  have hzi0c : 1 - star (z 0) * z i.succ ≠ 0 := by simpa [mul_comm] using hzi0
  have hz0jc : 1 - star (z j.succ) * z 0 ≠ 0 := by simpa [mul_comm] using hz0j
  have hw00c : 1 - star (w 0) * w 0 ≠ 0 := by simpa [mul_comm] using hw00
  have hden :
      (1 - z i.succ * star (z j.succ)) *
          (1 - z i.succ * star (z 0)) *
          (1 - z 0 * star (z j.succ)) *
          (1 - w 0 * star (w 0)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hzij hzi0) hz0j) hw00
  apply (eq_div_iff hden).2
  simp only [pickSchurComplementEntry, unitDiskPickKernel, inv_div]
  field_simp [hz00, hw00, hzij, hzi0, hz0j, hz00c, hzijc, hzi0c, hz0jc,
    hw00c]

/-- The common numerator is the difference of the value and node
    automorphism kernels, after clearing their four linear denominators. -/
theorem pickSchurComplementEntry_numerator_factor
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (i j : Fin N) :
    (1 - w i.succ * star (w j.succ)) *
          (1 - z i.succ * star (z 0)) *
          (1 - z 0 * star (z j.succ)) *
          (1 - w 0 * star (w 0)) -
        (1 - w i.succ * star (w 0)) *
          (1 - w 0 * star (w j.succ)) *
          (1 - z i.succ * star (z j.succ)) *
          (1 - z 0 * star (z 0)) =
      ((1 - w i.succ * star (w 0)) *
          (1 - w 0 * star (w j.succ)) *
          (1 - z i.succ * star (z 0)) *
          (1 - z 0 * star (z j.succ))) *
        ((1 - diskAutomorphism (w 0) (w i.succ) *
            star (diskAutomorphism (w 0) (w j.succ))) -
          (1 - reducedPickNode z i * star (reducedPickNode z j))) := by
  simp only [reducedPickNode]
  rw [one_sub_diskAutomorphism_mul_star (hw 0) (hw i.succ) (hw j.succ),
    one_sub_diskAutomorphism_mul_star (hz 0) (hz i.succ) (hz j.succ)]
  have hwi0 := one_sub_mul_star_ne_zero (hw i.succ) (hw 0)
  have hw0j := one_sub_mul_star_ne_zero (hw 0) (hw j.succ)
  have hzi0 := one_sub_mul_star_ne_zero (hz i.succ) (hz 0)
  have hz0j := one_sub_mul_star_ne_zero (hz 0) (hz j.succ)
  have hwi0c : 1 - star (w 0) * w i.succ ≠ 0 := by simpa [mul_comm] using hwi0
  have hw0jc : 1 - star (w j.succ) * w 0 ≠ 0 := by simpa [mul_comm] using hw0j
  have hzi0c : 1 - star (z 0) * z i.succ ≠ 0 := by simpa [mul_comm] using hzi0
  have hz0jc : 1 - star (z j.succ) * z 0 ≠ 0 := by simpa [mul_comm] using hz0j
  field_simp [hwi0, hw0j, hzi0, hz0j, hwi0c, hw0jc, hzi0c, hz0jc]

/-- Factored Schur-complement entry.  The final parenthesis is exactly the
    numerator occurring in `reducedPickKernel_quotient_formula`. -/
theorem pickSchurComplementEntry_formula
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (i j : Fin N) :
    pickSchurComplementEntry z w i j =
      ((1 - w i.succ * star (w 0)) *
          (1 - w 0 * star (w j.succ))) /
        ((1 - z i.succ * star (z j.succ)) *
          (1 - w 0 * star (w 0))) *
        ((1 - diskAutomorphism (w 0) (w i.succ) *
            star (diskAutomorphism (w 0) (w j.succ))) -
          (1 - reducedPickNode z i * star (reducedPickNode z j))) := by
  rw [pickSchurComplementEntry_commonDen_formula z w hz hw i j,
    pickSchurComplementEntry_numerator_factor z w hz hw i j]
  have hw00 := one_sub_mul_star_ne_zero (hw 0) (hw 0)
  have hzij := one_sub_mul_star_ne_zero (hz i.succ) (hz j.succ)
  have hzi0 := one_sub_mul_star_ne_zero (hz i.succ) (hz 0)
  have hz0j := one_sub_mul_star_ne_zero (hz 0) (hz j.succ)
  field_simp [hw00, hzij, hzi0, hz0j]

/-- Pick kernel of a pointwise quotient, with all divisions exposed only in
    this small algebraic lemma. -/
theorem quotientPickKernel_formula
    {zi zj ai aj : ℂ} (hzi : zi ≠ 0) (hzj : zj ≠ 0)
    (hk : 1 - zi * zj ≠ 0) :
    (1 - (ai / zi) * (aj / zj)) / (1 - zi * zj) =
      ((1 - ai * aj) - (1 - zi * zj)) /
        (zi * zj * (1 - zi * zj)) := by
  field_simp [hzi, hzj, hk]
  ring

theorem reducedPickNode_kernel_formula
    {N : ℕ} (z : Fin (N + 1) → ℂ) (hz : ∀ i, z i ∈ openUnitDisk)
    (i j : Fin N) :
    1 - reducedPickNode z i * star (reducedPickNode z j) =
      ((1 - z 0 * star (z 0)) * (1 - z i.succ * star (z j.succ))) /
        ((1 - star (z 0) * z i.succ) * (1 - z 0 * star (z j.succ))) := by
  exact one_sub_diskAutomorphism_mul_star (hz 0) (hz i.succ) (hz j.succ)

theorem reducedPickNode_mul_star_formula
    {N : ℕ} (z : Fin (N + 1) → ℂ) (hz : ∀ i, z i ∈ openUnitDisk)
    (i j : Fin N) :
    reducedPickNode z i * star (reducedPickNode z j) =
      ((z i.succ - z 0) * (star (z j.succ) - star (z 0))) /
        ((1 - star (z 0) * z i.succ) * (1 - z 0 * star (z j.succ))) := by
  have hstar : star (reducedPickNode z j) =
      (star (z j.succ) - star (z 0)) / (1 - z 0 * star (z j.succ)) := by
    simp [reducedPickNode, diskAutomorphism, mul_comm]
  rw [hstar]
  simp only [reducedPickNode, diskAutomorphism]
  have hdi := diskAutomorphism_den_ne_zero (hz 0) (hz i.succ)
  have hdj : 1 - z 0 * star (z j.succ) ≠ 0 :=
    one_sub_mul_star_ne_zero (hz 0) (hz j.succ)
  field_simp [hdi, hdj]

theorem reducedPickValue_numerator_kernel_formula
    {N : ℕ} (w : Fin (N + 1) → ℂ) (hw : ∀ i, w i ∈ openUnitDisk)
    (i j : Fin N) :
    1 - diskAutomorphism (w 0) (w i.succ) *
        star (diskAutomorphism (w 0) (w j.succ)) =
      ((1 - w 0 * star (w 0)) * (1 - w i.succ * star (w j.succ))) /
        ((1 - star (w 0) * w i.succ) * (1 - w 0 * star (w j.succ))) := by
  exact one_sub_diskAutomorphism_mul_star (hw 0) (hw i.succ) (hw j.succ)

theorem reducedPickKernel_quotient_formula
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hinj : Function.Injective z)
    (i j : Fin N) :
    unitDiskPickKernel (reducedPickNode z) (reducedPickValue z w) i j =
      ((1 - diskAutomorphism (w 0) (w i.succ) *
          star (diskAutomorphism (w 0) (w j.succ))) -
        (1 - reducedPickNode z i * star (reducedPickNode z j))) /
      (reducedPickNode z i * star (reducedPickNode z j) *
        (1 - reducedPickNode z i * star (reducedPickNode z j))) := by
  have hzi := reduced_den_node_ne_zero z hz hinj i
  have hzj := reduced_den_node_ne_zero z hz hinj j
  have hszj : star (reducedPickNode z j) ≠ 0 := star_ne_zero.mpr hzj
  have hk : 1 - reducedPickNode z i * star (reducedPickNode z j) ≠ 0 :=
    one_sub_mul_star_ne_zero
      (diskAutomorphism_mem_openUnitDisk (hz 0) (hz i.succ))
      (diskAutomorphism_mem_openUnitDisk (hz 0) (hz j.succ))
  have hq := quotientPickKernel_formula
    (zi := reducedPickNode z i) (zj := star (reducedPickNode z j))
    (ai := diskAutomorphism (w 0) (w i.succ))
    (aj := star (diskAutomorphism (w 0) (w j.succ))) hzi hszj hk
  simpa [unitDiskPickKernel, reducedPickValue] using hq

set_option maxHeartbeats 1000000 in
theorem reducedPickMatrix_eq_scaled_schurComplement
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (hinj : Function.Injective z) (i j : Fin N) :
    unitDiskPickKernel (reducedPickNode z) (reducedPickValue z w) i j =
      ((1 - w 0 * star (w 0)) / (1 - z 0 * star (z 0))) *
        star (pickReductionScale z w i) *
          pickSchurComplementEntry z w i j * pickReductionScale z w j := by
  rw [reducedPickKernel_quotient_formula z w hz hinj i j,
    pickSchurComplementEntry_formula z w hz hw i j,
    reducedPickNode_kernel_formula z hz i j,
    reducedPickNode_mul_star_formula z hz i j]
  have hscale : star (pickReductionScale z w i) =
      (1 - star (z 0) * z i.succ) ^ 2 /
        ((z i.succ - z 0) * (1 - star (w 0) * w i.succ)) := by
    simp [pickReductionScale, mul_comm]
  rw [hscale]
  simp only [pickReductionScale]
  have hz00 := one_sub_mul_star_ne_zero (hz 0) (hz 0)
  have hw00 := one_sub_mul_star_ne_zero (hw 0) (hw 0)
  have hzij := one_sub_mul_star_ne_zero (hz i.succ) (hz j.succ)
  have hzi0 := one_sub_mul_star_ne_zero (hz i.succ) (hz 0)
  have hz0j := one_sub_mul_star_ne_zero (hz 0) (hz j.succ)
  have hwi0 := one_sub_mul_star_ne_zero (hw i.succ) (hw 0)
  have hw0j := one_sub_mul_star_ne_zero (hw 0) (hw j.succ)
  have hdiffi : z i.succ - z 0 ≠ 0 := sub_ne_zero.mpr (hinj.ne (Fin.succ_ne_zero i))
  have hdiffj : star (z j.succ) - star (z 0) ≠ 0 := by
    simpa [star_sub] using star_ne_zero.mpr
      (sub_ne_zero.mpr (hinj.ne (Fin.succ_ne_zero j)))
  have hwi0c : 1 - star (w 0) * w i.succ ≠ 0 := by simpa [mul_comm] using hwi0
  field_simp [hz00, hw00, hzij, hzi0, hz0j, hwi0, hw0j, hwi0c,
    hdiffi, hdiffj, mul_comm]

theorem pickSchurComplement_posSemidef
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (hP : IsComplexPosSemidef (unitDiskPickKernel z w)) :
    IsComplexPosSemidef (fun i j : Fin N => pickSchurComplementEntry z w i j) := by
  exact complexPSD_schurComplement hP (pick_pivot_ne_zero z w (hz 0) (hw 0))

/-- Real scalar multiplying the diagonal congruence in the Schur reduction. -/
def pickReductionScalar {N : ℕ} (z w : Fin (N + 1) → ℂ) : ℝ :=
  (1 - ‖w 0‖ ^ 2) / (1 - ‖z 0‖ ^ 2)

theorem pickReductionScalar_nonneg
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : z 0 ∈ openUnitDisk) (hw : w 0 ∈ openUnitDisk) :
    0 ≤ pickReductionScalar z w := by
  unfold pickReductionScalar
  have hz' : ‖z 0‖ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg (z 0)) (by norm_num)).2 hz
  have hw' : ‖w 0‖ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg (w 0)) (by norm_num)).2 hw
  positivity

theorem pickReductionScalar_cast
    {N : ℕ} (z w : Fin (N + 1) → ℂ) :
    ((pickReductionScalar z w : ℝ) : ℂ) =
      (1 - w 0 * star (w 0)) / (1 - z 0 * star (z 0)) := by
  simp only [pickReductionScalar, Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, ofReal_div, ofReal_sub, ofReal_one, ofReal_pow,
    ofReal_norm]

/-- PSD transport through the nondegenerate Schur step. -/
theorem reducedPickMatrix_posSemidef
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (hinj : Function.Injective z)
    (hP : IsComplexPosSemidef (unitDiskPickKernel z w)) :
    IsComplexPosSemidef
      (unitDiskPickKernel (reducedPickNode z) (reducedPickValue z w)) := by
  classical
  let S : Matrix (Fin N) (Fin N) ℂ := fun i j => pickSchurComplementEntry z w i j
  let D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (pickReductionScale z w)
  have hS : IsComplexPosSemidef S := pickSchurComplement_posSemidef z w hz hw hP
  have hcongr : IsComplexPosSemidef (Matrix.conjTranspose D * S * D) :=
    hS.conjTranspose_mul_mul_same D
  have hscaled := hcongr.nonneg_real_smul
    (pickReductionScalar_nonneg z w (hz 0) (hw 0))
  have heq :
      ((pickReductionScalar z w : ℂ) •
          (Matrix.conjTranspose D * S * D)) =
        unitDiskPickKernel (reducedPickNode z) (reducedPickValue z w) := by
    ext i j
    dsimp only [D]
    change (pickReductionScalar z w : ℂ) *
      ((Matrix.conjTranspose (Matrix.diagonal (pickReductionScale z w)) * S *
        Matrix.diagonal (pickReductionScale z w)) i j) = _
    rw [Matrix.mul_diagonal]
    have hD : Matrix.conjTranspose (Matrix.diagonal (pickReductionScale z w)) =
        Matrix.diagonal (star (pickReductionScale z w)) := by
      ext r s
      by_cases hrs : r = s
      · subst s
        simp [Matrix.conjTranspose_apply]
      · simp [Matrix.conjTranspose_apply, Matrix.diagonal, hrs, Ne.symm hrs]
    rw [hD, Matrix.diagonal_mul]
    simp only [S]
    rw [pickReductionScalar_cast]
    simpa [mul_assoc] using
      (reducedPickMatrix_eq_scaled_schurComplement z w hz hw hinj i j).symm
  rw [← heq]
  exact hscaled

theorem reducedPickNode_mem_openUnitDisk
    {N : ℕ} (z : Fin (N + 1) → ℂ) (hz : ∀ i, z i ∈ openUnitDisk)
    (i : Fin N) : reducedPickNode z i ∈ openUnitDisk :=
  diskAutomorphism_mem_openUnitDisk (hz 0) (hz i.succ)

theorem reducedPickNode_ne_zero
    {N : ℕ} (z : Fin (N + 1) → ℂ) (hz : ∀ i, z i ∈ openUnitDisk)
    (hinj : Function.Injective z) (i : Fin N) : reducedPickNode z i ≠ 0 := by
  apply diskAutomorphism_ne_zero_of_ne (hz 0) (hz i.succ)
  exact hinj.ne (Fin.succ_ne_zero i)

theorem reducedPickNode_injective
    {N : ℕ} (z : Fin (N + 1) → ℂ) (hz : ∀ i, z i ∈ openUnitDisk)
    (hinj : Function.Injective z) : Function.Injective (reducedPickNode z) := by
  intro i j hij
  simp only [reducedPickNode, diskAutomorphism] at hij
  have hdi := diskAutomorphism_den_ne_zero (hz 0) (hz i.succ)
  have hdj := diskAutomorphism_den_ne_zero (hz 0) (hz j.succ)
  have hij' := (div_eq_div_iff hdi hdj).mp hij
  have : z i.succ = z j.succ := by
    have hz0 : 1 - z 0 * star (z 0) ≠ 0 :=
      one_sub_mul_star_ne_zero (hz 0) (hz 0)
    have hfac : (z i.succ - z j.succ) * (1 - star (z 0) * z 0) = 0 := by
      rw [show (z i.succ - z j.succ) * (1 - star (z 0) * z 0) =
        (z i.succ - z 0) * (1 - star (z 0) * z j.succ) -
          (z j.succ - z 0) * (1 - star (z 0) * z i.succ) by ring]
      exact sub_eq_zero.mpr hij'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (by simpa [mul_comm] using hz0))
  exact Fin.succ_inj.mp (hinj this)

theorem inverseSchurReconstruction_offPivot
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (hinj : Function.Injective z) (g : ℂ → ℂ) (i : Fin N)
    (hi : g (reducedPickNode z i) = reducedPickValue z w i) :
    inverseSchurReconstruction (z 0) (w 0) g (z i.succ) = w i.succ := by
  have hn := reducedPickNode_ne_zero z hz hinj i
  have hinner : reducedPickNode z i * g (reducedPickNode z i) =
      diskAutomorphism (w 0) (w i.succ) := by
    rw [hi]
    simp only [reducedPickValue]
    field_simp [hn]
  change diskAutomorphism (-w 0)
    (reducedPickNode z i * g (reducedPickNode z i)) = w i.succ
  rw [hinner]
  exact diskAutomorphism_inverse_neg (hw 0) (hw i.succ)

/-- A closed-Schur solution of the reduced problem reconstructs a solution of
    the original nondegenerate finite problem. -/
theorem hasClosedSchurSolution_of_reduced
    {N : ℕ} (z w : Fin (N + 1) → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hw : ∀ i, w i ∈ openUnitDisk)
    (hinj : Function.Injective z)
    (hred : HasClosedSchurSolution (reducedPickNode z) (reducedPickValue z w)) :
    HasClosedSchurSolution z w := by
  rcases hred with ⟨g, hga, hgb, hgi⟩
  let f := inverseSchurReconstruction (z 0) (w 0) g
  refine ⟨f, ?_, ?_, ?_⟩
  · exact inverseSchurReconstruction_analyticOnNhd (hz 0) (hw 0) hga hgb
  · exact inverseSchurReconstruction_bound (hz 0) (hw 0) hgb
  · intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · exact inverseSchurReconstruction_pivot (hz 0) (hw 0) g
    · exact inverseSchurReconstruction_offPivot z w hz hw hinj g i (hgi i)

/-- The finite Nevanlinna--Pick sufficiency direction needed by the RH chain. -/
theorem generalFiniteNevanlinnaPick_sufficient
    (N : ℕ) (z w : Fin N → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (hinj : Function.Injective z)
    (hP : IsComplexPosSemidef (unitDiskPickKernel z w)) :
    HasClosedSchurSolution z w := by
  induction N with
  | zero =>
      exact ⟨fun _ => 0, analyticOnNhd_const, by simp, fun i => Fin.elim0 i⟩
  | succ n ih =>
      have hwle : ∀ i, ‖w i‖ ≤ 1 := fun i =>
        pick_psd_target_norm_le_one hz hP i
      by_cases hboundary : ∃ k, ‖w k‖ = 1
      · obtain ⟨k, hk⟩ := hboundary
        exact hasClosedSchurSolution_of_pick_psd_boundary_value z w k hz hP hk
      · have hw : ∀ i, w i ∈ openUnitDisk := by
          intro i
          exact lt_of_le_of_ne (hwle i) (by
            intro hi
            exact hboundary ⟨i, hi⟩)
        have hred_psd := reducedPickMatrix_posSemidef z w hz hw hinj hP
        have hred_sol := ih (reducedPickNode z) (reducedPickValue z w)
          (reducedPickNode_mem_openUnitDisk z hz)
          (reducedPickNode_injective z hz hinj) hred_psd
        exact hasClosedSchurSolution_of_reduced z w hz hw hinj hred_sol

theorem interpolationDiskNode_mem_openUnitDisk (i : ℕ) :
    interpolationDiskNode i ∈ openUnitDisk := by
  unfold interpolationDiskNode openUnitDisk
  change ‖(((PickInterpolation.pickNode (i + 1) - 1) /
    (PickInterpolation.pickNode (i + 1) + 1) : ℝ) : ℂ)‖ < 1
  rw [norm_real, Real.norm_eq_abs, abs_of_pos]
  · rw [div_lt_one]
    · norm_num [PickInterpolation.pickNode]
      linarith
    · norm_num [PickInterpolation.pickNode]
      positivity
  · apply div_pos
    · norm_num [PickInterpolation.pickNode]
      have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    · norm_num [PickInterpolation.pickNode]
      positivity

theorem interpolationDiskNode_injective :
    Function.Injective interpolationDiskNode := by
  intro i j hij
  have hij' := congrArg Complex.re hij
  simp only [interpolationDiskNode, ofReal_re] at hij'
  simp only [PickInterpolation.pickNode] at hij'
  have hi : (5 / 2 + 2 * ((i : ℝ) + 1) + 1) ≠ 0 := by positivity
  have hj : (5 / 2 + 2 * ((j : ℝ) + 1) + 1) ≠ 0 := by positivity
  field_simp [hi, hj] at hij'
  norm_num [Nat.cast_add, Nat.cast_one] at hij'
  have : (i : ℝ) = (j : ℝ) := by linarith
  exact_mod_cast this

theorem hasClosedSchurSolution_fin_iff (N : ℕ) :
    HasClosedSchurSolution
        (fun i : Fin N => interpolationDiskNode i.val)
        (fun i : Fin N => boundaryDiskValue i.val) ↔
      HasFiniteSchurInterpolant N := by
  constructor
  · rintro ⟨f, hf, hb, hi⟩
    exact ⟨f, hf, hb, fun i hiN => hi ⟨i, hiN⟩⟩
  · rintro ⟨f, hf, hb, hi⟩
    exact ⟨f, hf, hb, fun i => hi i.val i.isLt⟩

theorem finitePickInterpolationFromPositivity_at_depth
    (N : ℕ)
    (hpos : Matrix.PosDef
      (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    HasFiniteSchurInterpolant N := by
  rw [← hasClosedSchurSolution_fin_iff]
  apply generalFiniteNevanlinnaPick_sufficient N
  · exact fun i => interpolationDiskNode_mem_openUnitDisk i.val
  · exact interpolationDiskNode_injective.comp Fin.val_injective
  · exact cayleyPickMatrixCompatibility_proved N hpos

/-- The general closed-Schur theorem specializes exactly to the concrete
    finite criterion used by the SEERAVERSE boundary data. -/
theorem finiteNevanlinnaPickCriterion_of_general
    (hgeneral : GeneralFiniteNevanlinnaPickCriterion) :
    FiniteNevanlinnaPickCriterion := by
  intro N
  rw [← hasClosedSchurSolution_fin_iff]
  exact hgeneral (ι := Fin N)
    (fun i : Fin N => interpolationDiskNode i.val)
    (fun i : Fin N => boundaryDiskValue i.val)
    (interpolationDiskNode_injective.comp Fin.val_injective)
    (fun i : Fin N => interpolationDiskNode_mem_openUnitDisk i.val)

/-- The empty interpolation problem is the base case of the finite Pick
    induction. -/
theorem finiteNevanlinnaPickCriterion_zero :
    IsComplexPosSemidef (diskPickMatrix 0) ↔
      HasFiniteSchurInterpolant 0 := by
  constructor
  · intro _
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · exact analyticOnNhd_const
    · intro z hz
      simp
    · intro i hi
      omega
  · intro _
    constructor
    · ext i
      exact Fin.elim0 i
    · intro x
      simp [dotProduct, Matrix.mulVec]

/-- A coherent choice of one finite Schur interpolant at every depth.  No
    compatibility between different depths is assumed. -/
structure FinitePickFamily where
  f : ℕ → ℂ → ℂ
  analytic : ∀ N, AnalyticOnNhd ℂ (f N) openUnitDisk
  schur_bound : ∀ N z, z ∈ openUnitDisk → ‖f N z‖ ≤ 1
  interpolates :
    ∀ N i, i < N → f N (interpolationDiskNode i) = boundaryDiskValue i

/-- Choosing one solution at every finite depth packages pointwise finite
    solvability as a `FinitePickFamily`. -/
theorem finitePickFamily_of_finite_solutions
    (hfinite : ∀ N : ℕ, HasFiniteSchurInterpolant N) :
    Nonempty FinitePickFamily := by
  classical
  choose f hf using hfinite
  refine ⟨{
    f := f
    analytic := fun N => (hf N).1
    schur_bound := fun N => (hf N).2.1
    interpolates := fun N => (hf N).2.2
  }⟩

/-- A fixed countable exhaustion of the unit disk by closed disks. -/
def schurExhaustion (m : ℕ) : Set ℂ :=
  Metric.closedBall 0 (1 - 1 / ((m : ℝ) + 2))

/-- Locally uniform convergence expressed on the fixed closed-disk
    exhaustion `schurExhaustion`. -/
def TendstoLocallyUniformlyOnUnitDisk
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ m : ℕ, TendstoUniformlyOn F f atTop (schurExhaustion m)

theorem schurExhaustion_compact (m : ℕ) :
    IsCompact (schurExhaustion m) := by
  exact isCompact_closedBall _ _

theorem schurExhaustion_subset_openUnitDisk (m : ℕ) :
    schurExhaustion m ⊆ openUnitDisk := by
  intro z hz
  rw [schurExhaustion, Metric.mem_closedBall, dist_zero_right] at hz
  rw [openUnitDisk, Set.mem_ofPred_eq]
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have hone : 0 < 1 / ((m : ℝ) + 2) := one_div_pos.mpr hden
  linarith

/-- A uniform derivative bound for every member of a finite Pick family on
    the `m`-th exhaustion disk. -/
theorem finitePickFamily_deriv_bound_on_exhaustion
    (F : FinitePickFamily) (m n : ℕ) {z : ℂ}
    (hz : z ∈ schurExhaustion m) :
    ‖deriv (F.f n) z‖ ≤ 4 * ((m : ℝ) + 2) := by
  let R : ℝ := 1 / (2 * ((m : ℝ) + 2))
  have hm2 : 0 < (m : ℝ) + 2 := by positivity
  have hR : 0 < R := by positivity
  have hz_norm : ‖z‖ ≤ 1 - 1 / ((m : ℝ) + 2) := by
    simpa [schurExhaustion, Metric.mem_closedBall, dist_zero_right] using hz
  have hball : Metric.ball z R ⊆ openUnitDisk := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rw [openUnitDisk, Set.mem_ofPred_eq]
    calc
      ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        simpa using norm_add_le (y - z) z
      _ < R + (1 - 1 / ((m : ℝ) + 2)) := add_lt_add_of_lt_of_le hy hz_norm
      _ < 1 := by
        have hR_eq : R = (1 / ((m : ℝ) + 2)) / 2 := by
          dsimp [R]
          field_simp [ne_of_gt hm2]
        rw [hR_eq]
        have : 0 < 1 / ((m : ℝ) + 2) := one_div_pos.mpr hm2
        nlinarith
  have hdiff : DifferentiableOn ℂ (F.f n) (Metric.ball z R) :=
    (F.analytic n).differentiableOn.mono hball
  have hmaps : Set.MapsTo (F.f n) (Metric.ball z R)
      (Metric.closedBall (F.f n z) 2) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖F.f n y - F.f n z‖ ≤ ‖F.f n y‖ + ‖F.f n z‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add
        (F.schur_bound n y (hball hy))
        (F.schur_bound n z (schurExhaustion_subset_openUnitDisk m hz))
      _ = 2 := by norm_num
  have hderiv := Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps hR
  calc
    ‖deriv (F.f n) z‖ ≤ 2 / R := hderiv
    _ = 4 * ((m : ℝ) + 2) := by
      dsimp [R]
      field_simp
      ring

/-- The family is uniformly Lipschitz, hence equicontinuous, on every member
    of the fixed exhaustion. -/
theorem finitePickFamily_lipschitzOn_exhaustion
    (F : FinitePickFamily) (m n : ℕ) :
    LipschitzOnWith ⟨4 * ((m : ℝ) + 2), by positivity⟩ (F.f n)
      (schurExhaustion m) := by
  apply (convex_closedBall (0 : ℂ) _).lipschitzOnWith_of_nnnorm_deriv_le
  · intro z hz
    exact ((F.analytic n) z
      (schurExhaustion_subset_openUnitDisk m hz)).differentiableAt
  · intro z hz
    exact_mod_cast finitePickFamily_deriv_bound_on_exhaustion F m n hz

theorem finitePickFamily_equicontinuousOn_exhaustion
    (F : FinitePickFamily) (m : ℕ) :
    EquicontinuousOn F.f (schurExhaustion m) := by
  exact (LipschitzOnWith.uniformEquicontinuousOn F.f
    ⟨4 * ((m : ℝ) + 2), by positivity⟩
    (finitePickFamily_lipschitzOn_exhaustion F m)).equicontinuousOn

theorem schurExhaustion_mono {m n : ℕ} (hmn : m ≤ n) :
    schurExhaustion m ⊆ schurExhaustion n := by
  intro z hz
  rw [schurExhaustion, Metric.mem_closedBall, dist_zero_right] at hz ⊢
  apply hz.trans
  have hm : 0 < (m : ℝ) + 2 := by positivity
  have hn : 0 < (n : ℝ) + 2 := by positivity
  have hcast : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
    exact_mod_cast Nat.add_le_add_right hmn 2
  have hinv : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := by
    exact one_div_le_one_div_of_le hm hcast
  linarith

/-- Every point of the open disk lies in the interior of one member of the
    fixed exhaustion. -/
theorem exists_schurExhaustion_mem_nhds {z : ℂ} (hz : z ∈ openUnitDisk) :
    ∃ m : ℕ, schurExhaustion m ∈ nhds z := by
  rw [openUnitDisk, Set.mem_ofPred_eq] at hz
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hz)
  refine ⟨m, Metric.closedBall_mem_nhds_of_mem ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hle : 1 / ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 1) := by
    gcongr
    norm_num
  linarith

/-- The fixed exhaustion is cofinal among compact subsets of the disk. -/
theorem compact_subset_schurExhaustion {K : Set ℂ}
    (hK : IsCompact K) (hKD : K ⊆ openUnitDisk) :
    ∃ m : ℕ, K ⊆ schurExhaustion m := by
  classical
  have hex : ∀ z : K, ∃ m : ℕ, schurExhaustion m ∈ nhds (z : ℂ) := by
    intro z
    exact exists_schurExhaustion_mem_nhds (hKD z.2)
  choose idx hidx using hex
  obtain ⟨t, hcover⟩ := hK.elim_nhds_subcover'
    (fun z hz => schurExhaustion (idx ⟨z, hz⟩))
    (fun z hz => hidx ⟨z, hz⟩)
  refine ⟨t.sup idx, ?_⟩
  intro z hz
  have hzU := hcover hz
  simp only [Set.mem_iUnion] at hzU
  obtain ⟨x, hxU⟩ := hzU
  obtain ⟨hxmem, hzx⟩ := hxU
  exact schurExhaustion_mono (Finset.le_sup hxmem) hzx

theorem iUnion_schurExhaustion :
    ⋃ m : ℕ, schurExhaustion m = openUnitDisk := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun m => schurExhaustion_subset_openUnitDisk m
  · intro z hz
    obtain ⟨m, hm⟩ := exists_schurExhaustion_mem_nhds hz
    exact Set.mem_iUnion.mpr ⟨m, mem_of_mem_nhds hm⟩

noncomputable instance : SigmaCompactSpace openUnitDisk := by
  constructor
  refine ⟨fun m => {z : openUnitDisk | (z : ℂ) ∈ schurExhaustion m}, ?_, ?_⟩
  · intro m
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have himage :
        ((↑) : openUnitDisk → ℂ) '' {z : openUnitDisk |
          (z : ℂ) ∈ schurExhaustion m} = schurExhaustion m := by
      apply Set.Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact hz
      · intro z hz
        exact ⟨⟨z, schurExhaustion_subset_openUnitDisk m hz⟩, hz, rfl⟩
    rw [himage]
    exact schurExhaustion_compact m
  · ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨m, hm⟩ := exists_schurExhaustion_mem_nhds z.2
    exact ⟨m, mem_of_mem_nhds hm⟩

noncomputable instance : LocallyCompactSpace openUnitDisk := by
  have hopen : IsOpen openUnitDisk := by
    simpa [openUnitDisk] using (isOpen_lt continuous_norm continuous_const)
  exact hopen.locallyCompactSpace

/-- Restriction of a finite Pick family to the open unit disk, bundled as
    continuous maps for compact-open Arzelà--Ascoli. -/
def finitePickFamilyContinuousMap (F : FinitePickFamily) (n : ℕ) :
    C(openUnitDisk, ℂ) where
  toFun z := F.f n z
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro z
    exact ((F.analytic n) z z.2).continuousAt.comp continuousAt_subtype_val

theorem finitePickFamily_equicontinuousOn_compact_subtype
    (F : FinitePickFamily) {K : Set openUnitDisk} (hK : IsCompact K) :
    EquicontinuousOn (fun n z => finitePickFamilyContinuousMap F n z) K := by
  have hKimage : IsCompact (((↑) : openUnitDisk → ℂ) '' K) :=
    hK.image continuous_subtype_val
  have hKD : ((↑) : openUnitDisk → ℂ) '' K ⊆ openUnitDisk := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  obtain ⟨m, hm⟩ := compact_subset_schurExhaustion hKimage hKD
  apply (LipschitzOnWith.uniformEquicontinuousOn
    (fun n z => finitePickFamilyContinuousMap F n z)
    ⟨4 * ((m : ℝ) + 2), by positivity⟩ ?_).equicontinuousOn
  intro n
  intro x hx y hy
  rw [show edist x y = edist (x : ℂ) (y : ℂ) by rfl]
  exact
    (finitePickFamily_lipschitzOn_exhaustion F m n
      (hm ⟨x, hx, rfl⟩) (hm ⟨y, hy, rfl⟩))

theorem finitePickFamily_compact_closure (F : FinitePickFamily) :
    IsCompact (closure (Set.range (finitePickFamilyContinuousMap F))) := by
  let S : Set C(openUnitDisk, ℂ) := Set.range (finitePickFamilyContinuousMap F)
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := {K : Set openUnitDisk | IsCompact K})
    (F := fun g : C(openUnitDisk, ℂ) => (g : openUnitDisk → ℂ))
  · intro K hK
    exact hK
  · refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [show (UniformOnFun.ofFun {K : Set openUnitDisk | IsCompact K} ∘
      fun g : C(openUnitDisk, ℂ) => (g : openUnitDisk → ℂ)) =
        ContinuousMap.toUniformOnFunIsCompact by rfl,
      ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous
      CompactlyCoherentSpace.isCoherentWith
  · intro K hK
    let pick : S → ℕ := fun g => Classical.choose g.2
    have hpick : ∀ g : S, finitePickFamilyContinuousMap F (pick g) = g := by
      intro g
      exact Classical.choose_spec g.2
    have heq := (finitePickFamily_equicontinuousOn_compact_subtype F hK).comp pick
    have hfun :
        (fun g : S => fun z => finitePickFamilyContinuousMap F (pick g) z) =
          (fun g : S => fun z => (g : C(openUnitDisk, ℂ)) z) := by
      funext g z
      exact DFunLike.congr_fun (hpick g) z
    change EquicontinuousOn
      (fun g : S => fun z => finitePickFamilyContinuousMap F (pick g) z) K at heq
    rw [hfun] at heq
    simpa [Function.comp_def] using heq
  · intro K hK x hx
    refine ⟨Metric.closedBall 0 1, isCompact_closedBall _ _, ?_⟩
    intro g hg
    obtain ⟨n, rfl⟩ := hg
    rw [Metric.mem_closedBall, dist_comm, dist_zero_left]
    exact F.schur_bound n x x.2

/-- Arzelà--Ascoli now supplies a single subsequence converging in the
    compact-open topology on the whole open unit disk; no diagonal argument
    is needed because this topology already encodes all compact subsets. -/
theorem finitePickFamily_has_compactOpen_subsequence (F : FinitePickFamily) :
    ∃ (g : C(openUnitDisk, ℂ)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => finitePickFamilyContinuousMap F (φ n)) atTop (nhds g) := by
  have hmem : ∀ n, finitePickFamilyContinuousMap F n ∈
      closure (Set.range (finitePickFamilyContinuousMap F)) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  obtain ⟨g, -, φ, hφ, hlim⟩ :=
    (finitePickFamily_compact_closure F).tendsto_subseq hmem
  exact ⟨g, φ, hφ, by simpa [Function.comp_def] using hlim⟩

noncomputable def projectToOpenUnitDisk (z : ℂ) : openUnitDisk := by
  classical
  exact if hz : z ∈ openUnitDisk then ⟨z, hz⟩ else ⟨0, by simp [openUnitDisk]⟩

@[simp] theorem projectToOpenUnitDisk_coe {z : ℂ} (hz : z ∈ openUnitDisk) :
    (projectToOpenUnitDisk z : ℂ) = z := by
  classical
  simp [projectToOpenUnitDisk, hz]

theorem exhaustionInDisk_compact (m : ℕ) :
    IsCompact {z : openUnitDisk | (z : ℂ) ∈ schurExhaustion m} := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have himage :
      ((↑) : openUnitDisk → ℂ) '' {z : openUnitDisk |
        (z : ℂ) ∈ schurExhaustion m} = schurExhaustion m := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · intro z hz
      exact ⟨⟨z, schurExhaustion_subset_openUnitDisk m hz⟩, hz, rfl⟩
  rw [himage]
  exact schurExhaustion_compact m

theorem compactOpen_tendsto_implies_exhaustion
    {F : FinitePickFamily} {φ : ℕ → ℕ} {g : C(openUnitDisk, ℂ)}
    (hlim : Tendsto (fun n => finitePickFamilyContinuousMap F (φ n))
      atTop (nhds g)) :
    TendstoLocallyUniformlyOnUnitDisk (fun n => F.f (φ n))
      (fun z => g (projectToOpenUnitDisk z)) := by
  intro m
  let K : Set openUnitDisk :=
    {z : openUnitDisk | (z : ℂ) ∈ schurExhaustion m}
  have hK : IsCompact K := exhaustionInDisk_compact m
  have hu : TendstoUniformlyOn
      (fun n z => finitePickFamilyContinuousMap F (φ n) z) g atTop K :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim) K hK
  have hc := hu.comp projectToOpenUnitDisk
  have hsubset : schurExhaustion m ⊆ projectToOpenUnitDisk ⁻¹' K := by
    intro z hz
    change (projectToOpenUnitDisk z : ℂ) ∈ schurExhaustion m
    rw [projectToOpenUnitDisk_coe (schurExhaustion_subset_openUnitDisk m hz)]
    exact hz
  have hc' := hc.mono hsubset
  have hleft : ∀ᶠ n in atTop, Set.EqOn
      ((fun z => finitePickFamilyContinuousMap F (φ n) z) ∘ projectToOpenUnitDisk)
      (F.f (φ n)) (schurExhaustion m) := by
    filter_upwards [] with n
    intro z hz
    change F.f (φ n) (projectToOpenUnitDisk z : ℂ) = F.f (φ n) z
    rw [projectToOpenUnitDisk_coe (schurExhaustion_subset_openUnitDisk m hz)]
  exact hc'.congr hleft

/-- Convergence on the fixed exhaustion is genuine locally uniform
    convergence on the open unit disk. -/
theorem tendstoLocallyUniformlyOn_of_exhaustion
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOnUnitDisk F f) :
    TendstoLocallyUniformlyOn F f atTop openUnitDisk := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  obtain ⟨m, hm⟩ := exists_schurExhaustion_mem_nhds hz
  exact ⟨schurExhaustion m, mem_nhdsWithin_of_mem_nhds hm,
    h m⟩

/-- The exhaustion-based form of Weierstrass' theorem: an exhaustion-uniform
    limit of analytic functions is analytic on the disk. -/
theorem analyticOnNhd_of_exhaustion_limit
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, AnalyticOnNhd ℂ (F n) openUnitDisk)
    (hlim : TendstoLocallyUniformlyOnUnitDisk F f) :
    AnalyticOnNhd ℂ f openUnitDisk := by
  have hopen : IsOpen openUnitDisk := by
    simpa [openUnitDisk] using (isOpen_lt continuous_norm continuous_const)
  have hlocal := tendstoLocallyUniformlyOn_of_exhaustion hlim
  have hdiff : DifferentiableOn ℂ f openUnitDisk :=
    hlocal.differentiableOn
      (Filter.Eventually.of_forall fun n => (hF n).differentiableOn)
      hopen
  exact hdiff.analyticOnNhd hopen

/-- Output interface for the normal-family/diagonal-subsequence theorem.
    Constructing this object from an arbitrary `FinitePickFamily` is the
    primary open compactness step. -/
structure SchurSubsequenceLimit (F : FinitePickFamily) where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  limit : ℂ → ℂ
  limit_analytic : AnalyticOnNhd ℂ limit openUnitDisk
  converges :
    TendstoLocallyUniformlyOnUnitDisk (fun n => F.f (index n)) limit

/-- The genuinely compactness-theoretic output.  Analyticity is deliberately
    omitted: it follows from `analyticOnNhd_of_exhaustion_limit`. -/
structure SchurConvergentSubsequence (F : FinitePickFamily) where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  limit : ℂ → ℂ
  converges :
    TendstoLocallyUniformlyOnUnitDisk (fun n => F.f (index n)) limit

def SchurConvergentSubsequence.toSubsequenceLimit
    {F : FinitePickFamily} (L : SchurConvergentSubsequence F) :
    SchurSubsequenceLimit F where
  index := L.index
  index_strictMono := L.index_strictMono
  limit := L.limit
  limit_analytic := analyticOnNhd_of_exhaustion_limit
    (fun n => F.analytic (L.index n)) L.converges
  converges := L.converges

namespace SchurSubsequenceLimit

theorem locallyUniform {F : FinitePickFamily} (L : SchurSubsequenceLimit F) :
    TendstoLocallyUniformlyOn (fun n => F.f (L.index n)) L.limit atTop
      openUnitDisk :=
  tendstoLocallyUniformlyOn_of_exhaustion L.converges

theorem limit_norm_le_one {F : FinitePickFamily} (L : SchurSubsequenceLimit F)
    {z : ℂ} (hz : z ∈ openUnitDisk) : ‖L.limit z‖ ≤ 1 := by
  have hpoint : Tendsto (fun n => F.f (L.index n) z) atTop
      (nhds (L.limit z)) := L.locallyUniform.tendsto_at hz
  exact le_of_tendsto' hpoint.norm (fun n => F.schur_bound (L.index n) z hz)

/-- Every fixed interpolation condition eventually occurs along a strictly
    increasing sequence of depths, hence survives the locally uniform limit. -/
theorem limit_interpolates {F : FinitePickFamily} (L : SchurSubsequenceLimit F)
    (i : ℕ) :
    L.limit (interpolationDiskNode i) = boundaryDiskValue i := by
  have hz : interpolationDiskNode i ∈ openUnitDisk :=
    interpolationDiskNode_mem_openUnitDisk i
  have hpoint : Tendsto
      (fun n => F.f (L.index n) (interpolationDiskNode i)) atTop
      (nhds (L.limit (interpolationDiskNode i))) :=
    L.locallyUniform.tendsto_at hz
  have heq : ∀ᶠ n in atTop,
      F.f (L.index n) (interpolationDiskNode i) = boundaryDiskValue i := by
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    apply F.interpolates
    exact lt_of_lt_of_le (Nat.lt_succ_self i)
      (hn.trans ((StrictMono.id_le L.index_strictMono) n))
  have hconst : Tendsto
      (fun n => F.f (L.index n) (interpolationDiskNode i)) atTop
      (nhds (boundaryDiskValue i)) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  exact tendsto_nhds_unique hpoint hconst

theorem limit_norm_lt_one_of_anchor {F : FinitePickFamily}
    (L : SchurSubsequenceLimit F) {a z : ℂ}
    (ha : a ∈ openUnitDisk) (ha_lt : ‖L.limit a‖ < 1)
    (hz : z ∈ openUnitDisk) : ‖L.limit z‖ < 1 := by
  by_contra hnot
  have hz_eq : ‖L.limit z‖ = 1 :=
    le_antisymm (L.limit_norm_le_one hz) (not_lt.mp hnot)
  have hmax : IsMaxOn (norm ∘ L.limit) openUnitDisk z := by
    intro y hy
    change ‖L.limit y‖ ≤ ‖L.limit z‖
    rw [hz_eq]
    exact L.limit_norm_le_one hy
  have hopen : IsOpen openUnitDisk := by
    simpa [openUnitDisk] using (isOpen_lt continuous_norm continuous_const)
  have hpre : IsPreconnected openUnitDisk := by
    have heq : openUnitDisk = Metric.ball (0 : ℂ) 1 := by
      ext x
      simp [openUnitDisk, mem_ball_zero_iff]
    rw [heq]
    exact (convex_ball (0 : ℂ) 1).isPreconnected
  have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hpre hopen
    L.limit_analytic.differentiableOn hz hmax ha
  change ‖L.limit a‖ = ‖L.limit z‖ at heq
  rw [hz_eq] at heq
  linarith

end SchurSubsequenceLimit

theorem boundaryDiskValue_zero_mem_openUnitDisk
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    boundaryDiskValue 0 ∈ openUnitDisk := by
  have hp : 0 < pickBoundaryRealValue 0 :=
    pickBoundaryRealValue_pos (h_pick_pos 1 (by omega)) 0
  rw [boundaryDiskValue_eq_cayley_R_boundary]
  apply cayleyTransform_mem_openUnitDisk_of_re_pos
  simpa [pickBoundaryRealValue] using hp

theorem SchurSubsequenceLimit.limit_mem_openUnitDisk
    {F : FinitePickFamily} (L : SchurSubsequenceLimit F)
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ))
    {z : ℂ} (hz : z ∈ openUnitDisk) :
    L.limit z ∈ openUnitDisk := by
  apply L.limit_norm_lt_one_of_anchor
    (interpolationDiskNode_mem_openUnitDisk 0) ?_ hz
  rw [L.limit_interpolates 0]
  exact boundaryDiskValue_zero_mem_openUnitDisk h_pick_pos

/-- The finite Nevanlinna--Pick theorem needed by this development, stated
    independently of the subsequent compactness argument. -/
def FinitePickInterpolationFromPositivity : Prop :=
  (∀ N : ℕ, 0 < N →
    Matrix.PosDef
      (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) →
  ∀ N : ℕ, HasFiniteSchurInterpolant N

theorem finitePickInterpolationFromPositivity_proved :
    FinitePickInterpolationFromPositivity := by
  intro h_pick_pos N
  by_cases hN : N = 0
  · subst N
    refine ⟨0, analyticOnNhd_const, by simp, ?_⟩
    intro i hi
    omega
  · exact finitePickInterpolationFromPositivity_at_depth N
      (h_pick_pos N (Nat.pos_of_ne_zero hN))

theorem finitePickFamily_of_all_depth_positivity
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    Nonempty FinitePickFamily :=
  finitePickFamily_of_finite_solutions
    (finitePickInterpolationFromPositivity_proved h_pick_pos)

/-- The Cayley matrix identity and the finite Nevanlinna--Pick criterion
    together discharge the finite-interpolant existence layer. -/
theorem finitePickInterpolationFromPositivity_of_criteria
    (hcayley : CayleyPickMatrixCompatibility)
    (hpick : FiniteNevanlinnaPickCriterion) :
    FinitePickInterpolationFromPositivity := by
  intro h_pick_pos N
  by_cases hN : 0 < N
  · exact (hpick N).mp (hcayley N (h_pick_pos N hN))
  · have hN0 : N = 0 := by omega
    subst N
    refine ⟨0, ?_, ?_, ?_⟩
    · exact analyticOnNhd_const
    · intro z hz
      simp
    · intro i hi
      omega

/-- After closing the Cayley matrix calculation, only the finite
    Nevanlinna--Pick existence criterion remains in the finite layer. -/
theorem finitePickInterpolationFromPositivity_of_pickCriterion
    (hpick : FiniteNevanlinnaPickCriterion) :
    FinitePickInterpolationFromPositivity :=
  finitePickInterpolationFromPositivity_of_criteria
    cayleyPickMatrixCompatibility_proved hpick

/-- The exact normal-family compactness statement needed after finite
    interpolants have been selected. -/
def SchurNormalFamilyCompactness : Prop :=
  ∀ F : FinitePickFamily, Nonempty (SchurSubsequenceLimit F)

/-- A minimal formulation of the remaining Montel step: it asks only for a
    locally uniformly convergent subsequence.  Weierstrass' theorem supplies
    analyticity automatically. -/
def SchurNormalFamilySequentialCompactness : Prop :=
  ∀ F : FinitePickFamily, Nonempty (SchurConvergentSubsequence F)

theorem schurNormalFamilySequentialCompactness_proved :
    SchurNormalFamilySequentialCompactness := by
  intro F
  obtain ⟨g, φ, hφ, hlim⟩ := finitePickFamily_has_compactOpen_subsequence F
  exact ⟨{
    index := φ
    index_strictMono := hφ
    limit := fun z => g (projectToOpenUnitDisk z)
    converges := compactOpen_tendsto_implies_exhaustion hlim
  }⟩

theorem schurNormalFamilyCompactness_of_sequential
    (h : SchurNormalFamilySequentialCompactness) :
    SchurNormalFamilyCompactness := by
  intro F
  obtain ⟨L⟩ := h F
  exact ⟨L.toSubsequenceLimit⟩

theorem schurNormalFamilyCompactness_proved :
    SchurNormalFamilyCompactness :=
  schurNormalFamilyCompactness_of_sequential
    schurNormalFamilySequentialCompactness_proved

/-- Finite Pick solvability and normal-family compactness reduce all-depth
    positivity to a locally uniformly convergent analytic subsequence. -/
theorem schur_subsequence_limit_of_all_depth_positivity
    (hfinite : FinitePickInterpolationFromPositivity)
    (hcompact : SchurNormalFamilyCompactness)
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    ∃ F : FinitePickFamily, Nonempty (SchurSubsequenceLimit F) := by
  obtain ⟨F⟩ := finitePickFamily_of_finite_solutions (hfinite h_pick_pos)
  exact ⟨F, hcompact F⟩

/-- With finite NP sufficiency now proved, normal-family compactness is the
    only remaining input for constructing a Schur subsequence limit. -/
theorem schur_subsequence_limit_of_all_depth_positivity_proved
    (hcompact : SchurNormalFamilyCompactness)
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    ∃ F : FinitePickFamily, Nonempty (SchurSubsequenceLimit F) := by
  obtain ⟨F⟩ := finitePickFamily_of_all_depth_positivity h_pick_pos
  exact ⟨F, hcompact F⟩

/-- Explicit real formula for the `i`-th Cayley Pick node: `diskPickNode i = (4 * i - 1) / (4 * i + 3)`. -/
theorem diskPickNode_formula (i : ℕ) :
    diskPickNode i = ((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℂ) := by
  unfold diskPickNode halfPlaneToDisk PickInterpolation.pickNode
  dsimp
  push_cast
  field_simp
  ring

/-- Every Cayley Pick node `diskPickNode i` lies in the open unit disk `openUnitDisk`. -/
theorem diskPickNode_mem_openUnitDisk (i : ℕ) :
    diskPickNode i ∈ openUnitDisk := by
  rw [openUnitDisk, Set.mem_ofPred_eq, diskPickNode_formula]
  have hi : 0 ≤ (i : ℝ) := by positivity
  have h_den_pos : 0 < 4 * (i : ℝ) + 3 := by linarith
  have hnorm : ‖((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℂ)‖ = |(4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3)| := by
    rw [show ((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℂ) = (((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, abs_div, abs_of_pos h_den_pos, div_lt_iff₀ h_den_pos]
  rw [abs_lt]
  constructor <;> linarith

/-- The far-right half-plane is open. -/
theorem isOpen_farRightHalfPlane : IsOpen farRightHalfPlane := by
  simpa [farRightHalfPlane] using (isOpen_lt continuous_const Complex.continuous_re)

/-- `diskToHalfPlane` maps `openUnitDisk` into `farRightHalfPlane`. -/
theorem diskToHalfPlane_mem {w : ℂ} (hw : w ∈ openUnitDisk) :
    diskToHalfPlane w ∈ farRightHalfPlane := by
  have hwnorm : ‖w‖ < 1 := by simpa [openUnitDisk] using hw
  have hw1 : w ≠ 1 := by
    intro h
    subst w
    norm_num at hwnorm
  have hden : 0 < Complex.normSq (1 - w) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hw1))
  have hsq : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hratio : 0 < ((1 + w) / (1 - w)).re := by
    rw [Complex.div_re]
    have hnum :
        (1 + w).re * (1 - w).re + (1 + w).im * (1 - w).im =
          1 - Complex.normSq w := by
      simp [Complex.normSq]
      ring
    rw [← add_div, hnum]
    exact div_pos (sub_pos.mpr hsq) hden
  rw [farRightHalfPlane, Set.mem_ofPred_eq, diskToHalfPlane]
  simpa using hratio

/-- `halfPlaneToDisk` maps `farRightHalfPlane` into `openUnitDisk`. -/
theorem halfPlaneToDisk_mem {z : ℂ} (hz : z ∈ farRightHalfPlane) :
    halfPlaneToDisk z ∈ openUnitDisk := by
  rw [openUnitDisk, Set.mem_ofPred_eq, halfPlaneToDisk]
  dsimp [farRightHalfPlane] at hz
  have h_norm3_pos : 0 < ‖z - 3‖ := by
    rw [norm_pos_iff]
    intro h
    have hre := congr_arg Complex.re h
    dsimp at hre
    linarith
  rw [norm_div, div_lt_iff₀ h_norm3_pos, one_mul]
  rw [Complex.norm_def, Complex.norm_def]
  have h_re5 : (z - 5).re = z.re - 5 := by simp
  have h_im5 : (z - 5).im = z.im := by simp
  have h_re3 : (z - 3).re = z.re - 3 := by simp
  have h_im3 : (z - 3).im = z.im := by simp
  have h_sq : (z - 5).re * (z - 5).re + (z - 5).im * (z - 5).im < (z - 3).re * (z - 3).re + (z - 3).im * (z - 3).im := by
    rw [h_re5, h_im5, h_re3, h_im3]
    nlinarith
  have h_nonneg5 : 0 ≤ (z - 5).re * (z - 5).re + (z - 5).im * (z - 5).im := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact Real.sqrt_lt_sqrt h_nonneg5 h_sq





/-- Differentiability of `diskToHalfPlane` at any point `w ≠ 1`. -/
theorem diskToHalfPlane_differentiableAt {w : ℂ} (hw : w ≠ 1) :
    DifferentiableAt ℂ diskToHalfPlane w := by
  unfold diskToHalfPlane
  have h1 : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  apply DifferentiableAt.add
  · fun_prop
  · apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact h1

/-- `diskPullback g` is analytic on the open unit disk `openUnitDisk`. -/
theorem diskPullback_analyticOnNhd_openUnitDisk {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g farRightHalfPlane) :
    AnalyticOnNhd ℂ (diskPullback g) openUnitDisk := by
  have hopen_disk : IsOpen openUnitDisk := by
    simpa [openUnitDisk] using (isOpen_lt continuous_norm continuous_const)
  have hpull_diff : DifferentiableOn ℂ (diskPullback g) openUnitDisk := by
    intro w hw
    have hw1 : w ≠ 1 := by
      intro h; subst h; rw [openUnitDisk, Set.mem_ofPred_eq] at hw; simp at hw
    have himage : diskToHalfPlane w ∈ farRightHalfPlane := diskToHalfPlane_mem hw
    have hg_at : DifferentiableAt ℂ g (diskToHalfPlane w) :=
      (hg _ himage).differentiableAt (isOpen_farRightHalfPlane.mem_nhds himage)
    have hmap : DifferentiableAt ℂ diskToHalfPlane w := diskToHalfPlane_differentiableAt hw1
    have hcomp : DifferentiableAt ℂ (g ∘ diskToHalfPlane) w := hg_at.comp w hmap
    exact hcomp.differentiableWithinAt
  exact hpull_diff.analyticOnNhd hopen_disk

/-- Bound transport: `diskPullback g` is bounded on `openUnitDisk` by the same bound `M`. -/
theorem diskPullback_bounded_openUnitDisk {g : ℂ → ℂ}
    (hg_bdd : ∃ M : ℝ, ∀ z ∈ farRightHalfPlane, ‖g z‖ ≤ M) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ w ∈ openUnitDisk, ‖diskPullback g w‖ ≤ M := by
  rcases hg_bdd with ⟨M, hM⟩
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro w hw
  have himage : diskToHalfPlane w ∈ farRightHalfPlane := diskToHalfPlane_mem hw
  have hb := hM (diskToHalfPlane w) himage
  unfold diskPullback
  exact hb.trans (le_max_right _ _)

/-- `diskPullback g` is analytic on the closed disk `Metric.closedBall 0 R` for every `0 ≤ R < 1`. -/
theorem diskPullback_analyticOnNhd_closedBall {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g farRightHalfPlane) {R : ℝ} (_hR : 0 ≤ R) (hR1 : R < 1) :
    AnalyticOnNhd ℂ (diskPullback g) (Metric.closedBall 0 R) := by
  apply (diskPullback_analyticOnNhd_openUnitDisk hg).mono
  intro w hw
  have hw_norm : ‖w‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  rw [openUnitDisk, Set.mem_ofPred_eq]
  linarith

/-- Bound transport for `diskPullback g` on the sphere `Metric.sphere 0 R` for any `0 ≤ R < 1`. -/
theorem diskPullback_bound_on_sphere {g : ℂ → ℂ}
    (hg_bdd : ∃ M : ℝ, ∀ z ∈ farRightHalfPlane, ‖g z‖ ≤ M) {R : ℝ} (_hR : 0 ≤ R) (hR1 : R < 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖diskPullback g z‖ ≤ M := by
  rcases diskPullback_bounded_openUnitDisk hg_bdd with ⟨M, hM1, hM_bound⟩
  refine ⟨M, hM1, ?_⟩
  intro z hz
  have hz_norm : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
  have hz_disk : z ∈ openUnitDisk := by
    rw [openUnitDisk, Set.mem_ofPred_eq, hz_norm]
    exact hR1
  exact hM_bound z hz_disk

/-- Jensen evaluation radius for $N$ nodes: `jensenRadius N = (4 * N + 1) / (4 * N + 3) < 1`. -/
def jensenRadius (N : ℕ) : ℝ :=
  (4 * (N : ℝ) + 1) / (4 * (N : ℝ) + 3)

/-- The `i`-th Cayley Pick node norm `‖diskPickNode i‖` is strictly strictly less than `jensenRadius N` for `1 ≤ i ≤ N`. -/
theorem diskPickNode_lt_jensenRadius (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    ‖diskPickNode i‖ < jensenRadius N := by
  rw [diskPickNode_formula]
  have hi_real : 1 ≤ (i : ℝ) := by exact Nat.one_le_cast.mpr hi
  have hN_real : (i : ℝ) ≤ (N : ℝ) := by exact Nat.cast_le.mpr hiN
  have h_den_i : 0 < 4 * (i : ℝ) + 3 := by linarith
  have h_den_N : 0 < 4 * (N : ℝ) + 3 := by linarith
  have h_pos_num : 0 < 4 * (i : ℝ) - 1 := by linarith
  have hnorm : ‖((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℂ)‖ = (4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) := by
    have h_cast : ((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℂ) = (((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [h_cast, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos h_pos_num, abs_of_pos h_den_i]
  rw [hnorm, jensenRadius]
  rw [div_lt_div_iff₀ h_den_i h_den_N]
  nlinarith

/-- Positivity of `jensenRadius N`. -/
theorem jensenRadius_pos (N : ℕ) :
    0 < jensenRadius N := by
  unfold jensenRadius
  have hN : 0 ≤ (N : ℝ) := by positivity
  positivity

/-- Lower bound on `N * log (jensenRadius N) > -1/2`. -/
theorem jensenRadius_log_lower (N : ℕ) :
    -(1 / 2 : ℝ) < (N : ℝ) * Real.log (jensenRadius N) := by
  have hRpos : 0 < jensenRadius N := jensenRadius_pos N
  have h_inv_pos : 0 < (jensenRadius N)⁻¹ := inv_pos.mpr hRpos
  have h_log_inv : Real.log ((jensenRadius N)⁻¹) ≤ (jensenRadius N)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos h_inv_pos
  have h_log_neg : -Real.log (jensenRadius N) ≤ (jensenRadius N)⁻¹ - 1 := by
    rwa [Real.log_inv] at h_log_inv
  have h_inv_sub : (jensenRadius N)⁻¹ - 1 = 2 / (4 * (N : ℝ) + 1) := by
    unfold jensenRadius
    have h1 : 0 < 4 * (N : ℝ) + 1 := by positivity
    have h3 : 0 < 4 * (N : ℝ) + 3 := by positivity
    field_simp
    ring
  rw [h_inv_sub] at h_log_neg
  have h_log_lower : - (2 / (4 * (N : ℝ) + 1)) ≤ Real.log (jensenRadius N) := by linarith
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have h_mul := mul_le_mul_of_nonneg_left h_log_lower hN_nonneg
  have h_bound : -(1 / 2 : ℝ) < (N : ℝ) * -(2 / (4 * (N : ℝ) + 1)) := by
    have h1 : 0 < 4 * (N : ℝ) + 1 := by positivity
    have h_ineq : (N : ℝ) * 2 / (4 * (N : ℝ) + 1) < 1 / 2 := by
      rw [div_lt_div_iff₀ h1 (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have h_alg : (N : ℝ) * -(2 / (4 * (N : ℝ) + 1)) = - ((N : ℝ) * 2 / (4 * (N : ℝ) + 1)) := by ring
    rw [h_alg]
    linarith
  linarith

/-- Unboundedness of the logarithmic denominator term `log ((4N+3)/3)` as $N \to \infty$. -/
theorem jensen_log_term_unbounded (C : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ C < Real.log ((4 * (N : ℝ) + 3) / 3) := by
  have hexp_pos : 0 < 3 * Real.exp C := by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max 1 (3 * Real.exp C))
  have h1 : (1 : ℝ) ≤ max 1 (3 * Real.exp C) := le_max_left 1 _
  have h2 : (3 * Real.exp C) ≤ max 1 (3 * Real.exp C) := le_max_right 1 _
  have hgt1 : 1 < (N0 : ℝ) := h1.trans_lt hN0
  have hgt2 : 3 * Real.exp C < (N0 : ℝ) := h2.trans_lt hN0
  have hN1 : 1 ≤ N0 := Nat.one_le_cast.mp hgt1.le
  refine ⟨N0, hN1, ?_⟩
  have h_den_pos : 0 < (4 * (N0 : ℝ) + 3) / 3 := by positivity
  have hexp_lt : Real.exp C < (4 * (N0 : ℝ) + 3) / 3 := by linarith
  rwa [Real.lt_log_iff_exp_lt h_den_pos]

/-- The weighted Pick zero contribution in the Jensen formula is unbounded as $N \to \infty$. -/
theorem pick_jensen_weight_unbounded (C : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ C < (N : ℝ) * Real.log (jensenRadius N) + Real.log ((4 * (N : ℝ) + 3) / 3) := by
  obtain ⟨N, hN1, hN⟩ := jensen_log_term_unbounded (C + 1 / 2)
  have hfirst := jensenRadius_log_lower N
  refine ⟨N, hN1, ?_⟩
  linarith

/-- The pullback function `diskPullback g` vanishes at every Cayley Pick node `diskPickNode i`. -/
theorem diskPullback_zero_at_diskPickNode (g : ℂ → ℂ)
    (hg_zero : ∀ i : ℕ, g (PickInterpolation.pickNode (i + 1) : ℂ) = 0) (i : ℕ) :
    diskPullback g (diskPickNode i) = 0 := by
  unfold diskPullback diskPickNode
  have hnode : (PickInterpolation.pickNode (i + 1) : ℂ) ≠ 3 := by
    dsimp [PickInterpolation.pickNode]
    push_cast
    intro h
    have hre : (5 / 2 + 2 * ((i : ℝ) + 1) : ℝ) = 3 := by
      have := congr_arg Complex.re h
      simpa using this
    linarith
  rw [diskToHalfPlane_halfPlaneToDisk _ hnode]
  exact hg_zero i

/-- Circle average upper bound for bounded meromorphic functions. -/
theorem diskPullback_circleAverage_log_norm_le {G : ℂ → ℂ} {M R : ℝ}
    (hM : 1 ≤ M)
    (hGmer : MeromorphicOn G (Metric.closedBall (0 : ℂ) R))
    (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖G z‖ ≤ M)
    (hR : 0 ≤ R) :
    Real.circleAverage (fun z : ℂ => Real.log ‖G z‖) 0 R ≤ Real.log M := by
  have h_sphere_mer : MeromorphicOn G (Metric.sphere (0 : ℂ) |R|) := by
    rw [abs_of_nonneg hR]
    exact fun z hz => hGmer z (Metric.sphere_subset_closedBall hz)
  have hint : CircleIntegrable (fun z : ℂ => Real.log ‖G z‖) 0 R :=
    h_sphere_mer.circleIntegrable_log_norm
  have hbound_abs : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, Real.log ‖G z‖ ≤ Real.log M := by
    intro z hz
    rw [abs_of_nonneg hR] at hz
    have hzM := hbound z hz
    by_cases hz0 : ‖G z‖ = 0
    · rw [hz0, Real.log_zero]
      exact Real.log_nonneg hM
    · have hpos : 0 < ‖G z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
      exact Real.log_le_log hpos hzM
  exact Real.circleAverage_mono_on_of_le_circle hint hbound_abs

/-- The divisor of G at every Pick node diskPickNode i is at least 1. -/
theorem diskPickNode_divisor_ge_one {G : ℂ → ℂ}
    (hGan : AnalyticOnNhd ℂ G openUnitDisk)
    (hGnot : ¬ Set.EqOn G 0 openUnitDisk)
    (hzero : ∀ i, G (diskPickNode i) = 0)
    (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    1 ≤ (MeromorphicOn.divisor G (Metric.closedBall 0 (jensenRadius N))) (diskPickNode i) := by
  have hRpos : 0 < jensenRadius N := jensenRadius_pos N
  have hR_lt1 : jensenRadius N < 1 := by
    unfold jensenRadius
    have hN_real : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr (by omega)
    have hnum : 0 < 4 * (N : ℝ) + 1 := by linarith
    have hden : 0 < 4 * (N : ℝ) + 3 := by linarith
    rw [div_lt_iff₀ hden]; linarith
  have hG_ball_an : AnalyticOnNhd ℂ G (Metric.closedBall 0 (jensenRadius N)) := by
    apply hGan.mono
    intro w hw
    have hw_norm : ‖w‖ ≤ jensenRadius N := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
    rw [openUnitDisk, Set.mem_ofPred_eq]
    linarith
  have hi_lt : ‖diskPickNode i‖ < jensenRadius N := diskPickNode_lt_jensenRadius N i hi hiN
  have hi_ball : diskPickNode i ∈ Metric.closedBall (0 : ℂ) (jensenRadius N) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hi_lt.le
  have hi_disk : diskPickNode i ∈ openUnitDisk := diskPickNode_mem_openUnitDisk i
  have h_div_eq : MeromorphicOn.divisor G (Metric.closedBall 0 (jensenRadius N)) (diskPickNode i) =
      (meromorphicOrderAt G (diskPickNode i)).untop₀ := by
    exact MeromorphicOn.divisor_apply hG_ball_an.meromorphicOn hi_ball
  rw [h_div_eq]
  have hAan : AnalyticAt ℂ G (diskPickNode i) := hGan (diskPickNode i) hi_disk
  have hzero_i : G (diskPickNode i) = 0 := hzero i
  have horder_ne0 : analyticOrderAt G (diskPickNode i) ≠ 0 := by
    exact (AnalyticAt.analyticOrderAt_ne_zero hAan).mpr hzero_i
  have horder_ne_top : analyticOrderAt G (diskPickNode i) ≠ ⊤ := by
    intro htop
    have h_ev : ∀ᶠ z in nhds (diskPickNode i), G z = 0 := by
      rwa [analyticOrderAt_eq_top] at htop
    have h_pre : IsPreconnected openUnitDisk := by
      have hball : openUnitDisk = Metric.ball (0 : ℂ) 1 := by
        ext w; simp [openUnitDisk, Metric.mem_ball, dist_zero_right]
      rw [hball]
      exact (convex_ball (0 : ℂ) 1).isPreconnected
    have h_freq : ∃ᶠ z in nhdsWithin (diskPickNode i) {diskPickNode i}ᶜ, G z = 0 :=
      (h_ev.filter_mono nhdsWithin_le_nhds).frequently
    have h_eq0 : Set.EqOn G 0 openUnitDisk :=
      hGan.eqOn_zero_of_preconnected_of_frequently_eq_zero h_pre hi_disk h_freq
    exact hGnot h_eq0
  rw [hAan.meromorphicOrderAt_eq]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt G (diskPickNode i) = k := by
    cases h : analyticOrderAt G (diskPickNode i) with
    | top => exact False.elim (horder_ne_top h)
    | coe k => exact ⟨k, rfl⟩
  rw [hk]
  have hk_pos : 0 < k := by
    by_contra h0
    have : k = 0 := by omega
    subst this
    simp at hk
    exact horder_ne0 hk
  exact Nat.one_le_cast.mpr hk_pos

/-- Lower bound on the Jensen zero contribution by the finite sum over Pick nodes. -/
theorem pick_sum_le_jensen_finsum {G : ℂ → ℂ}
    (hGan : AnalyticOnNhd ℂ G openUnitDisk)
    (hGnot : ¬ Set.EqOn G 0 openUnitDisk)
    (hzero : ∀ i, G (diskPickNode i) = 0)
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ Finset.Icc 1 N, Real.log (jensenRadius N * ‖diskPickNode i‖⁻¹) ≤
      ∑ᶠ u : ℂ, ((MeromorphicOn.divisor G (Metric.closedBall 0 (jensenRadius N))) u : ℤ) *
        Real.log (jensenRadius N * ‖u‖⁻¹) := by
  let R := jensenRadius N
  let CB := Metric.closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor G CB
  have hDfin : (D).support.Finite := (D).finiteSupport (isCompact_closedBall 0 R)
  let SD : Finset ℂ := hDfin.toFinset
  have hfinsum : (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) * Real.log (R * ‖u‖⁻¹)) =
      ∑ u ∈ SD, ((D u : ℤ) : ℝ) * Real.log (R * ‖u‖⁻¹) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    have huD : D u ≠ 0 := by
      intro h0
      apply hu
      simp [h0]
    change u ∈ hDfin.toFinset
    exact hDfin.mem_toFinset.mpr huD
  rw [hfinsum]
  let SN : Finset ℂ := (Finset.Icc 1 N).image diskPickNode
  have hSN_inj : Set.InjOn diskPickNode (Finset.Icc 1 N) := by
    intro i hi j hj h
    rw [diskPickNode_formula, diskPickNode_formula] at h
    have h_real : (4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) = (4 * (j : ℝ) - 1) / (4 * (j : ℝ) + 3) := by exact_mod_cast h
    have hi_pos : 0 < 4 * (i : ℝ) + 3 := by positivity
    have hj_pos : 0 < 4 * (j : ℝ) + 3 := by positivity
    have h_mul : (4 * (i : ℝ) - 1) * (4 * (j : ℝ) + 3) = (4 * (j : ℝ) - 1) * (4 * (i : ℝ) + 3) := by
      field_simp [hi_pos.ne', hj_pos.ne'] at h_real
      simpa [mul_comm] using h_real
    have h_ij : (i : ℝ) = (j : ℝ) := by nlinarith
    exact Nat.cast_injective h_ij
  have hsum_SN : (∑ i ∈ Finset.Icc 1 N, Real.log (R * ‖diskPickNode i‖⁻¹)) =
      ∑ u ∈ SN, Real.log (R * ‖u‖⁻¹) := by
    rw [Finset.sum_image hSN_inj]
  rw [hsum_SN]
  have hSN_sub_SD : SN ⊆ SD := by
    intro u hu
    rw [Finset.mem_image] at hu
    rcases hu with ⟨i, hi, rfl⟩
    rw [Finset.mem_Icc] at hi
    rw [hDfin.mem_toFinset]
    have hge1 := diskPickNode_divisor_ge_one hGan hGnot hzero N i hi.1 hi.2
    intro h0
    rw [h0] at hge1
    linarith
  have h_le : ∑ u ∈ SN, Real.log (R * ‖u‖⁻¹) ≤ ∑ u ∈ SD, ((D u : ℤ) : ℝ) * Real.log (R * ‖u‖⁻¹) := by
    have h_bound_SN : ∑ u ∈ SN, Real.log (R * ‖u‖⁻¹) ≤ ∑ u ∈ SN, ((D u : ℤ) : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      apply Finset.sum_le_sum
      intro u hu_SN
      rw [Finset.mem_image] at hu_SN
      rcases hu_SN with ⟨i, hi, rfl⟩
      rw [Finset.mem_Icc] at hi
      have hge1 := diskPickNode_divisor_ge_one hGan hGnot hzero N i hi.1 hi.2
      have hlog_pos : 0 ≤ Real.log (R * ‖diskPickNode i‖⁻¹) := by
        have hlt := diskPickNode_lt_jensenRadius N i hi.1 hi.2
        have hpos : 0 < ‖diskPickNode i‖ := by
          have hi1 : 1 ≤ (i : ℝ) := Nat.one_le_cast.mpr hi.1
          rw [diskPickNode_formula]
          have hnum : 0 < 4 * (i : ℝ) - 1 := by linarith
          have hden : 0 < 4 * (i : ℝ) + 3 := by linarith
          have h_real : ((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℂ) = (((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℝ) : ℂ) := by push_cast; rfl
          rw [h_real, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hnum hden)]
          exact div_pos hnum hden
        have h1 : 1 < R * ‖diskPickNode i‖⁻¹ := by
          rw [show R * ‖diskPickNode i‖⁻¹ = R / ‖diskPickNode i‖ from (div_eq_mul_inv R ‖diskPickNode i‖).symm]
          rw [one_lt_div₀ hpos]
          exact hlt
        exact (Real.log_pos h1).le
      have hD_real : 1 ≤ ((D (diskPickNode i) : ℤ) : ℝ) := by exact_mod_cast hge1
      nlinarith
    have h_bound_SD : ∑ u ∈ SN, ((D u : ℤ) : ℝ) * Real.log (R * ‖u‖⁻¹) ≤ ∑ u ∈ SD, ((D u : ℤ) : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSN_sub_SD
      intro u hu_SD hu_notSN
      have huD : D u ≠ 0 := by
        rw [hDfin.mem_toFinset] at hu_SD
        exact hu_SD
      have hu_CB : u ∈ CB := by
        by_contra hu
        exact huD (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hu)
      have hD_nonneg : 0 ≤ D u := by
        have h_ball_an : AnalyticOnNhd ℂ G CB := by
          apply hGan.mono
          intro w hw
          have hw_norm : ‖w‖ ≤ R := by
            simpa [CB, Metric.mem_closedBall, dist_zero_right] using hw
          rw [openUnitDisk, Set.mem_ofPred_eq]
          have hR_lt1 : R < 1 := by
            dsimp [R]
            unfold jensenRadius
            have hN_real : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
            have hnum : 0 < 4 * (N : ℝ) + 1 := by linarith
            have hden : 0 < 4 * (N : ℝ) + 3 := by linarith
            rw [div_lt_iff₀ hden]; linarith
          linarith
        rw [MeromorphicOn.divisor_apply h_ball_an.meromorphicOn hu_CB]
        have h_nonneg := (h_ball_an u hu_CB).meromorphicOrderAt_nonneg
        cases horder : meromorphicOrderAt G u with
        | top => simp
        | coe n =>
          simp only [WithTop.untop₀_coe]
          have : 0 ≤ n := by
            rw [horder] at h_nonneg
            exact WithTop.coe_le_coe.mp h_nonneg
          exact_mod_cast this
      have hlog_nonneg : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
        by_cases hu0 : ‖u‖ = 0
        · rw [hu0, inv_zero, mul_zero, Real.log_zero]
        · have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
          have hu_le : ‖u‖ ≤ R := by
            simpa [CB, Metric.mem_closedBall, dist_zero_right] using hu_CB
          have h1 : 1 ≤ R * ‖u‖⁻¹ := by
            rw [show R * ‖u‖⁻¹ = R / ‖u‖ from (div_eq_mul_inv R ‖u‖).symm]
            rw [one_le_div₀ hpos]
            exact hu_le
          exact Real.log_nonneg h1
      positivity
    exact h_bound_SN.trans h_bound_SD
  exact h_le

/-- Lower bound on the Jensen center correction term. -/
theorem jensen_center_correction_lower {G : ℂ → ℂ}
    (hGan : AnalyticOnNhd ℂ G openUnitDisk)
    (hGnot : ¬ Set.EqOn G 0 openUnitDisk) :
    ∃ C0 : ℝ, ∀ N : ℕ, 1 ≤ N →
      C0 ≤ ((meromorphicOrderAt G 0).untop₀ : ℝ) * Real.log (jensenRadius N) +
        Real.log ‖meromorphicTrailingCoeffAt G 0‖ := by
  have h0_disk : (0 : ℂ) ∈ openUnitDisk := by simp [openUnitDisk]
  have hA0 : AnalyticAt ℂ G 0 := hGan 0 h0_disk
  have hm0 : 0 ≤ (meromorphicOrderAt G 0).untop₀ := by
    have h_nonneg := hA0.meromorphicOrderAt_nonneg
    cases horder : meromorphicOrderAt G 0 with
    | top => simp
    | coe n =>
      simp only [WithTop.untop₀_coe]
      have : 0 ≤ (n : ℤ) := by
        rw [horder] at h_nonneg
        exact WithTop.coe_le_coe.mp h_nonneg
      exact this
  let m : ℤ := (meromorphicOrderAt G 0).untop₀
  let C0 : ℝ := (m : ℝ) * Real.log (5 / 7) + Real.log ‖meromorphicTrailingCoeffAt G 0‖
  refine ⟨C0, fun N hN => ?_⟩
  have hR1 : (5 / 7 : ℝ) ≤ jensenRadius N := by
    unfold jensenRadius
    have hN1 : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hnum : 0 < 4 * (N : ℝ) + 1 := by linarith
    have hden : 0 < 4 * (N : ℝ) + 3 := by linarith
    rw [div_le_div_iff₀ (by norm_num) hden]
    nlinarith
  have hlog : Real.log (5 / 7) ≤ Real.log (jensenRadius N) := Real.log_le_log (by norm_num) hR1
  have hmul : (m : ℝ) * Real.log (5 / 7) ≤ (m : ℝ) * Real.log (jensenRadius N) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith


theorem pick_log_telescope (N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ Finset.Icc 1 N,
        Real.log ((4 * (i : ℝ) + 3) / (4 * (i : ℝ) - 1))
      =
    Real.log ((4 * (N : ℝ) + 3) / 3) := by
  induction' N, hN using Nat.le_induction with n hn ih
  · norm_num
  · have hsplit :
        Finset.Icc 1 (n + 1) = Finset.Icc 1 n ∪ {n + 1} := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
      omega
    have hdisj : Disjoint (Finset.Icc 1 n) {n + 1} := by
      simp only [Finset.disjoint_singleton_right, Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_singleton, ih]
    push_cast
    have hA : 0 < (4 * (n : ℝ) + 3) / 3 := by positivity
    have hB :
        0 <
          (4 * ((n : ℝ) + 1) + 3) /
            (4 * ((n : ℝ) + 1) - 1) := by
      have hnR : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      apply div_pos <;> linarith
    have hc :
        4 * (n : ℝ) + 3 =
          4 * ((n : ℝ) + 1) - 1 := by
      ring
    have hprod :
        ((4 * (n : ℝ) + 3) / 3) *
            ((4 * ((n : ℝ) + 1) + 3) / (4 * ((n : ℝ) + 1) - 1)) =
          (4 * ((n : ℝ) + 1) + 3) / 3 := by
      rw [← hc]
      field_simp
    rw [← Real.log_mul hA.ne' hB.ne', hprod]

theorem pick_jensen_finite_sum_eq
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ Finset.Icc 1 N,
        Real.log (jensenRadius N * ‖diskPickNode i‖⁻¹)
      =
    (N : ℝ) * Real.log (jensenRadius N) +
      Real.log ((4 * (N : ℝ) + 3) / 3) := by
  have hterm :
      ∀ i ∈ Finset.Icc 1 N,
        Real.log (jensenRadius N * ‖diskPickNode i‖⁻¹) =
          Real.log (jensenRadius N) +
            Real.log ((4 * (i : ℝ) + 3) /
              (4 * (i : ℝ) - 1)) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hnum : 0 < 4 * (i : ℝ) - 1 := by
      have : 1 ≤ (i : ℝ) := Nat.one_le_cast.mpr hi.1
      linarith
    have hden : 0 < 4 * (i : ℝ) + 3 := by positivity
    have hnorm :
        ‖diskPickNode i‖ =
          (4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) := by
      rw [diskPickNode_formula]
      have hreal :
          ((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℂ) =
            (((4 * (i : ℝ) - 1) / (4 * (i : ℝ) + 3) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hreal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos hnum hden)]
    rw [hnorm, inv_div]
    rw [Real.log_mul
      (jensenRadius_pos N).ne'
      (div_pos hden hnum).ne']
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hc :
      ∑ _i ∈ Finset.Icc 1 N, Real.log (jensenRadius N) =
        (N : ℝ) * Real.log (jensenRadius N) := by
    rw [Finset.sum_const, Nat.card_Icc]
    have hcard : N + 1 - 1 = N := by omega
    rw [hcard, nsmul_eq_mul]
  rw [hc, pick_log_telescope N hN]

/-- Rigidity for bounded holomorphic functions on `farRightHalfPlane` vanishing on Pick nodes. -/
theorem bounded_holomorphic_zero_rigidity (g : ℂ → ℂ)
    (hg_holo : DifferentiableOn ℂ g farRightHalfPlane)
    (hg_bdd : ∃ M : ℝ, ∀ z ∈ farRightHalfPlane, ‖g z‖ ≤ M)
    (hg_zero : ∀ i : ℕ, g (PickInterpolation.pickNode (i + 1) : ℂ) = 0) :
    Set.EqOn g 0 farRightHalfPlane := by
  let G : ℂ → ℂ := diskPullback g
  have hGan : AnalyticOnNhd ℂ G openUnitDisk := diskPullback_analyticOnNhd_openUnitDisk hg_holo
  have hGzero : ∀ i : ℕ, G (diskPickNode i) = 0 := fun i => diskPullback_zero_at_diskPickNode g hg_zero i
  have hG_ident : Set.EqOn G 0 openUnitDisk := by
    by_contra hGnot
    obtain ⟨M, hM1, hMbdd⟩ := diskPullback_bounded_openUnitDisk hg_bdd
    obtain ⟨C0, hC0⟩ := jensen_center_correction_lower hGan hGnot
    obtain ⟨N, hN1, hNbig⟩ := pick_jensen_weight_unbounded (Real.log M - C0)
    have hRpos : 0 < jensenRadius N := jensenRadius_pos N
    have hR_lt1 : jensenRadius N < 1 := by
      unfold jensenRadius
      have hN_real : 1 ≤ (N : ℝ) := Nat.one_le_cast.mpr hN1
      have hnum : 0 < 4 * (N : ℝ) + 1 := by linarith
      have hden : 0 < 4 * (N : ℝ) + 3 := by linarith
      rw [div_lt_iff₀ hden]
      linarith
    have hG_ball_an : AnalyticOnNhd ℂ G (Metric.closedBall 0 (jensenRadius N)) :=
      diskPullback_analyticOnNhd_closedBall hg_holo hRpos.le hR_lt1
    have hG_sphere_bdd : ∀ z ∈ Metric.sphere (0 : ℂ) (jensenRadius N), ‖G z‖ ≤ M := by
      intro z hz
      rw [Metric.mem_sphere, dist_zero_right] at hz
      have hz_disk : z ∈ openUnitDisk := by
        rw [openUnitDisk, Set.mem_ofPred_eq, hz]
        exact hR_lt1
      exact hMbdd z hz_disk
    have hAvg_le : Real.circleAverage (fun z : ℂ => Real.log ‖G z‖) 0 (jensenRadius N) ≤ Real.log M :=
      diskPullback_circleAverage_log_norm_le hM1 hG_ball_an.meromorphicOn hG_sphere_bdd hRpos.le
    have hG_ball_an' : MeromorphicOn G (Metric.closedBall 0 |jensenRadius N|) := by
      rw [abs_of_pos hRpos]
      exact hG_ball_an.meromorphicOn
    have hJensen_eq := MeromorphicOn.circleAverage_log_norm (show jensenRadius N ≠ 0 from hRpos.ne') hG_ball_an'
    have hPick_le := pick_sum_le_jensen_finsum hGan hGnot hGzero N hN1
    have hCenter_le := hC0 N hN1
    have h0_div : (MeromorphicOn.divisor G (Metric.closedBall 0 |jensenRadius N|)) 0 = (meromorphicOrderAt G 0).untop₀ := by
      rw [abs_of_pos hRpos]
      exact MeromorphicOn.divisor_apply hG_ball_an.meromorphicOn (by simp [Metric.mem_closedBall, hRpos.le])
    have h_log_sum_eq := pick_jensen_finite_sum_eq N hN1
    have hPick_le' :
      ∑ i ∈ Finset.Icc 1 N,
        Real.log (jensenRadius N * ‖diskPickNode i‖⁻¹)
        ≤
      ∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor G
          (Metric.closedBall 0 |jensenRadius N|) u : ℤ) : ℝ) *
        Real.log
          (jensenRadius N * ‖0 - u‖⁻¹) := by
      rw [abs_of_pos hRpos]
      simpa using hPick_le
    rw [h0_div] at hJensen_eq
    have h_Jensen_add : Real.circleAverage (fun x ↦ Real.log ‖G x‖) 0 (jensenRadius N) =
        (∑ᶠ (u : ℂ), ↑((MeromorphicOn.divisor G (Metric.closedBall 0 |jensenRadius N|)) u) * Real.log (jensenRadius N * ‖0 - u‖⁻¹)) +
        ↑(meromorphicOrderAt G 0).untop₀ * Real.log (jensenRadius N) + Real.log ‖meromorphicTrailingCoeffAt G 0‖ := hJensen_eq
    have h_bound_all : (N : ℝ) * Real.log (jensenRadius N) + Real.log ((4 * (N : ℝ) + 3) / 3) + C0 ≤ Real.log M := by
      calc (N : ℝ) * Real.log (jensenRadius N) + Real.log ((4 * (N : ℝ) + 3) / 3) + C0
        _ = (∑ i ∈ Finset.Icc 1 N, Real.log (jensenRadius N * ‖diskPickNode i‖⁻¹)) + C0 := by rw [h_log_sum_eq]
        _ ≤ (∑ᶠ (u : ℂ), ↑((MeromorphicOn.divisor G (Metric.closedBall 0 |jensenRadius N|)) u) * Real.log (jensenRadius N * ‖0 - u‖⁻¹)) + (↑(meromorphicOrderAt G 0).untop₀ * Real.log (jensenRadius N) + Real.log ‖meromorphicTrailingCoeffAt G 0‖) := by linarith [hPick_le', hCenter_le]
        _ = (∑ᶠ (u : ℂ), ↑((MeromorphicOn.divisor G (Metric.closedBall 0 |jensenRadius N|)) u) * Real.log (jensenRadius N * ‖0 - u‖⁻¹)) + ↑(meromorphicOrderAt G 0).untop₀ * Real.log (jensenRadius N) + Real.log ‖meromorphicTrailingCoeffAt G 0‖ := by ring
        _ = Real.circleAverage (fun x ↦ Real.log ‖G x‖) 0 (jensenRadius N) := h_Jensen_add.symm
        _ ≤ Real.log M := hAvg_le
    linarith

  intro z hz
  have hw : halfPlaneToDisk z ∈ openUnitDisk := halfPlaneToDisk_mem hz
  have hGz : G (halfPlaneToDisk z) = 0 := hG_ident hw
  unfold G diskPullback at hGz
  have hz3 : z ≠ 3 := by
    intro h
    subst h
    dsimp [farRightHalfPlane] at hz
    linarith
  rwa [diskToHalfPlane_halfPlaneToDisk z hz3] at hGz

/-- Reduction of Nevanlinna-class zero rigidity to bounded holomorphic zero rigidity. -/
theorem nevanlinna_pick_zero_rigidity {f : ℂ → ℂ}
    (hN : IsNevanlinnaOn f farRightHalfPlane)
    (hzeros : ∀ i : ℕ, f (PickInterpolation.pickNode (i + 1) : ℂ) = 0) :
    Set.EqOn f 0 farRightHalfPlane := by
  rcases hN with ⟨g, h, hg_holo, _hh_holo, hg_bdd, _hh_bdd, hh_ne, hquot⟩
  have hg_zero : ∀ i : ℕ, g (PickInterpolation.pickNode (i + 1) : ℂ) = 0 := by
    intro i
    have hi : (PickInterpolation.pickNode (i + 1) : ℂ) ∈ farRightHalfPlane := pickNode_in_farRightHalfPlane i
    have hq := hquot (PickInterpolation.pickNode (i + 1) : ℂ) hi
    have hz := hzeros i
    have hhne := hh_ne (PickInterpolation.pickNode (i + 1) : ℂ) hi
    rw [hz] at hq
    have : g (PickInterpolation.pickNode (i + 1) : ℂ) / h (PickInterpolation.pickNode (i + 1) : ℂ) = 0 := hq.symm
    exact (div_eq_zero_iff.mp this).resolve_right hhne
  have hg_ident : Set.EqOn g 0 farRightHalfPlane :=
    bounded_holomorphic_zero_rigidity g hg_holo hg_bdd hg_zero
  intro z hz
  rw [hquot z hz]
  have hg_z : g z = 0 := hg_ident hz
  dsimp at hg_z ⊢
  rw [hg_z, zero_div]

/-- Rigidity on the far-right half-plane (paper eq 9.13):
    If `D = H - R_boundary` is of Nevanlinna class on `H₄` and vanishes on the Pick lattice,
    then `D ≡ 0` on `H₄`. -/
theorem rigidityDifference_eq_zero_on_farRightHalfPlane
    (H : ℂ → ℂ)
    (hN : IsNevanlinnaOn (rigidityDifference H) farRightHalfPlane)
    (h_match : ∀ (i : ℕ), H (PickInterpolation.pickNode (i + 1) : ℂ) = R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)) :
    Set.EqOn (rigidityDifference H) 0 farRightHalfPlane := by
  have hzeros : ∀ i : ℕ, rigidityDifference H (PickInterpolation.pickNode (i + 1) : ℂ) = 0 :=
    rigidityDifference_zero_at_pickNodes H h_match
  exact nevanlinna_pick_zero_rigidity hN hzeros

/-- Right half-plane is connected/preconnected. -/
theorem isPreconnected_rightHalfPlane : IsPreconnected rightHalfPlane := by
  simpa [rightHalfPlane] using (convex_halfSpace_re_gt 0).isPreconnected

/-- Meromorphic identity continuation from `H₄` to the whole right half-plane:
    equality is obtained on punctured neighborhoods, which is the natural notion for meromorphic functions (paper §9.4). -/
theorem meromorphic_identity_continuation {F H : ℂ → ℂ}
    (hF : MeromorphicOn F rightHalfPlane)
    (hH : MeromorphicOn H rightHalfPlane)
    (hEq4 : Set.EqOn F H farRightHalfPlane) :
    ∀ x ∈ rightHalfPlane, F =ᶠ[nhdsWithin x {x}ᶜ] H := by
  let M : ℂ → ℂ := fun z => F z - H z
  have hM : MeromorphicOn M rightHalfPlane := hF.sub hH
  have h5R : (5 : ℂ) ∈ rightHalfPlane := by simp [rightHalfPlane]
  have h5F : (5 : ℂ) ∈ farRightHalfPlane := by
    change 4 < (5 : ℂ).re
    norm_num
  have hfar_nhds : farRightHalfPlane ∈ nhds (5 : ℂ) := isOpen_farRightHalfPlane.mem_nhds h5F
  have hM_zero_nhds : ∀ᶠ z : ℂ in nhds (5 : ℂ), M z = 0 := by
    filter_upwards [hfar_nhds] with z hz
    dsimp [M]
    rw [hEq4 hz, sub_self]
  have hM_zero_nhdsNE : ∀ᶠ z : ℂ in nhdsWithin (5 : ℂ) {(5 : ℂ)}ᶜ, M z = 0 :=
    eventually_nhdsWithin_of_eventually_nhds hM_zero_nhds
  have horder5 : meromorphicOrderAt M (5 : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    exact hM_zero_nhdsNE
  intro x hx
  have horderx : meromorphicOrderAt M x = ⊤ :=
    hM.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_rightHalfPlane h5R hx horder5
  have hzero : ∀ᶠ z : ℂ in nhdsWithin x {x}ᶜ, M z = 0 := by
    rwa [meromorphicOrderAt_eq_top_iff] at horderx
  filter_upwards [hzero] with z hz
  dsimp [M] at hz
  exact sub_eq_zero.mp hz

/-- The right half-plane is open. -/
theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane := by
  simpa [rightHalfPlane] using (isOpen_lt continuous_const Complex.continuous_re)

/-- Eventual equality with a holomorphic function on punctured neighborhoods excludes poles. -/
theorem pole_free_of_eventuallyEq_holomorphic {F H : ℂ → ℂ} (hH : DifferentiableOn ℂ H rightHalfPlane)
    (hEq : ∀ x ∈ rightHalfPlane, F =ᶠ[nhdsWithin x {x}ᶜ] H) : ∀ x : ℂ, 0 < x.re → ¬ PoleExclusion.HasPoleAt F x := by
  intro x hx hpole
  have hx_mem : x ∈ rightHalfPlane := by simpa [rightHalfPlane] using hx
  have hnhds : rightHalfPlane ∈ nhds x := isOpen_rightHalfPlane.mem_nhds hx_mem
  have hH_cont : ContinuousAt H x := by
    have hd : DifferentiableWithinAt ℂ H rightHalfPlane x := hH x hx_mem
    exact hd.continuousWithinAt.continuousAt hnhds
  have hnormH : Tendsto (fun z : ℂ => ‖H z‖) (nhdsWithin x {x}ᶜ) (nhds ‖H x‖) := hH_cont.norm.mono_left inf_le_left
  have heq := hEq x hx_mem
  have hnormEq : (fun z : ℂ => ‖F z‖) =ᶠ[nhdsWithin x {x}ᶜ] (fun z : ℂ => ‖H z‖) :=
    heq.fun_comp (fun w : ℂ => ‖w‖)
  have hnormF : Tendsto (fun z : ℂ => ‖F z‖) (nhdsWithin x {x}ᶜ) (nhds ‖H x‖) :=
    hnormH.congr' hnormEq.symm
  exact (not_tendsto_nhds_of_tendsto_atTop hpole ‖H x‖) hnormF

/-- Equality with a holomorphic function on the right half-plane excludes poles there. -/
theorem pole_free_of_eq_holomorphic {F H : ℂ → ℂ} (hH : DifferentiableOn ℂ H rightHalfPlane)
    (hEq : ∀ z : ℂ, 0 < z.re → F z = H z) : ∀ x : ℂ, 0 < x.re → ¬ PoleExclusion.HasPoleAt F x := by
  apply pole_free_of_eventuallyEq_holomorphic hH
  intro x hx
  have hnhds : rightHalfPlane ∈ nhds x := isOpen_rightHalfPlane.mem_nhds hx
  have h_rhp : ∀ᶠ z : ℂ in nhdsWithin x {x}ᶜ, z ∈ rightHalfPlane := eventually_nhdsWithin_of_eventually_nhds hnhds
  filter_upwards [h_rhp] with z hz
  exact hEq z (by simpa [rightHalfPlane] using hz)

/-- Rigidity Step B for the actual boundary function. -/
theorem R_boundary_pole_free_of_interpolant (H : ℂ → ℂ) (h_holo : DifferentiableOn ℂ H rightHalfPlane)
    (_h_pos_real : IsPositiveRealOn H rightHalfPlane)
    (_h_match : ∀ (i : ℕ), H (PickInterpolation.pickNode (i + 1) : ℂ) = R_boundary (PickInterpolation.pickNode (i + 1) : ℂ))
    (h_identity : ∀ x ∈ rightHalfPlane, R_boundary =ᶠ[nhdsWithin x {x}ᶜ] H) :
    ∀ x : ℂ, 0 < x.re → ¬ PoleExclusion.HasPoleAt R_boundary x := by
  exact pole_free_of_eventuallyEq_holomorphic h_holo h_identity

/-- The completed zeta function is meromorphic everywhere.  Writing it in
    terms of Mathlib's entire `completedRiemannZeta₀` makes the two possible
    poles explicit. -/
theorem Lambda_meromorphic : Meromorphic Lambda := by
  change Meromorphic completedRiemannZeta
  rw [show completedRiemannZeta = fun s : ℂ =>
      completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) by
    funext s
    exact completedRiemannZeta_eq s]
  intro z
  have hzero : MeromorphicAt completedRiemannZeta₀ z :=
    (differentiable_completedZeta₀.analyticAt z).meromorphicAt
  have hone : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) z := by fun_prop
  have hid : MeromorphicAt (fun s : ℂ => s) z := by fun_prop
  have hsub : MeromorphicAt (fun s : ℂ => 1 - s) z := by fun_prop
  exact (hzero.sub (hone.div hid)).sub (hone.div hsub)

theorem xi_meromorphic : Meromorphic xi := by
  have hc : Meromorphic (fun _ : ℂ => (1 / 2 : ℂ)) := by fun_prop
  have hid : Meromorphic (fun z : ℂ => z) := by fun_prop
  have hsub : Meromorphic (fun z : ℂ => z - 1) := by fun_prop
  exact (((hc.mul hid).mul hsub).mul Lambda_meromorphic)

theorem logDeriv_xi_meromorphic : Meromorphic (logDeriv xi) :=
  xi_meromorphic.logDeriv

/-- The concrete boundary transform is meromorphic on the right half-plane;
    zeros of its explicit denominator are permitted by `MeromorphicOn.div`. -/
theorem R_boundary_meromorphic_on_rightHalfPlane :
    MeromorphicOn R_boundary rightHalfPlane := by
  intro z hz
  change MeromorphicAt
    (fun x : ℂ =>
      ((1 / 2 + x) * (1 / 2 + x - 1) * logDeriv xi (1 / 2 + x) -
        kappa * (2 * (1 / 2 + x) - 1)) /
      ((1 / 2 + x - 3) * (1 / 2 + x + 2))) z
  have hs : MeromorphicAt (fun x : ℂ => 1 / 2 + x) z := by fun_prop
  have hlog : MeromorphicAt (fun x : ℂ => logDeriv xi (1 / 2 + x)) z := by
    simpa [Function.comp_def] using
      (logDeriv_xi_meromorphic (1 / 2 + z)).comp_analyticAt (by fun_prop)
  fun_prop

/-- Positive-real function obtained from a strict Schur limit by the two
    Cayley maps appropriate to the full right half-plane. -/
def halfPlaneInterpolant {F : FinitePickFamily}
    (L : SchurSubsequenceLimit F) (z : ℂ) : ℂ :=
  invCayleyTransform (L.limit (rightHalfPlaneToDisk z))

theorem rightHalfPlaneToDisk_pickNode (i : ℕ) :
    rightHalfPlaneToDisk
        (PickInterpolation.pickNode (i + 1) : ℂ) =
      interpolationDiskNode i := by
  simp only [rightHalfPlaneToDisk, interpolationDiskNode]
  norm_cast

theorem halfPlaneInterpolant_differentiableOn
    {F : FinitePickFamily} (L : SchurSubsequenceLimit F)
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    DifferentiableOn ℂ (halfPlaneInterpolant L) rightHalfPlane := by
  intro z hz
  have hm : rightHalfPlaneToDisk z ∈ openUnitDisk :=
    rightHalfPlaneToDisk_mem_openUnitDisk hz
  have hlm : L.limit (rightHalfPlaneToDisk z) ∈ openUnitDisk :=
    L.limit_mem_openUnitDisk h_pick_pos hm
  exact ((invCayleyTransform_analyticOnNhd _ hlm).differentiableAt.comp z
    ((L.limit_analytic _ hm).differentiableAt.comp z
      (rightHalfPlaneToDisk_analyticOnNhd z hz).differentiableAt)).differentiableWithinAt

theorem halfPlaneInterpolant_isPositiveRealOn
    {F : FinitePickFamily} (L : SchurSubsequenceLimit F)
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    IsPositiveRealOn (halfPlaneInterpolant L) rightHalfPlane := by
  intro z hz
  apply invCayleyTransform_re_pos
  exact L.limit_mem_openUnitDisk h_pick_pos
    (rightHalfPlaneToDisk_mem_openUnitDisk hz)

theorem halfPlaneInterpolant_isNevanlinnaOn_farRightHalfPlane
    {F : FinitePickFamily} (L : SchurSubsequenceLimit F)
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    IsNevanlinnaOn (halfPlaneInterpolant L) farRightHalfPlane := by
  let f : ℂ → ℂ := fun z => L.limit (rightHalfPlaneToDisk z)
  have hsubset : farRightHalfPlane ⊆ rightHalfPlane := by
    intro z hz
    dsimp [farRightHalfPlane, rightHalfPlane] at hz ⊢
    linarith
  have hfa : DifferentiableOn ℂ f farRightHalfPlane := by
    intro z hz
    have hm := rightHalfPlaneToDisk_mem_openUnitDisk (hsubset hz)
    exact ((L.limit_analytic _ hm).differentiableAt.comp z
      (rightHalfPlaneToDisk_analyticOnNhd z (hsubset hz)).differentiableAt).differentiableWithinAt
  have hfb : ∀ z ∈ farRightHalfPlane, ‖f z‖ ≤ 1 := by
    intro z hz
    exact L.limit_norm_le_one
      (rightHalfPlaneToDisk_mem_openUnitDisk (hsubset hz))
  have hfs : ∀ z ∈ farRightHalfPlane, ‖f z‖ < 1 := by
    intro z hz
    exact L.limit_mem_openUnitDisk h_pick_pos
      (rightHalfPlaneToDisk_mem_openUnitDisk (hsubset hz))
  exact invCayley_isNevanlinnaOn hfa hfb hfs

theorem halfPlaneInterpolant_matches
    {F : FinitePickFamily} (L : SchurSubsequenceLimit F)
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ))
    (i : ℕ) :
    halfPlaneInterpolant L
        (PickInterpolation.pickNode (i + 1) : ℂ) =
      R_boundary (PickInterpolation.pickNode (i + 1) : ℂ) := by
  have hp : 0 < pickBoundaryRealValue i :=
    pickBoundaryRealValue_pos (h_pick_pos (i + 1) (by omega)) ⟨i, by omega⟩
  have hne : R_boundary
      (PickInterpolation.pickNode (i + 1) : ℂ) ≠ -1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [pickBoundaryRealValue, h] at hp
    linarith
  rw [halfPlaneInterpolant, rightHalfPlaneToDisk_pickNode,
    L.limit_interpolates, boundaryDiskValue_eq_cayley_R_boundary]
  exact cayley_involutive _ hne

/-- The part of the Montel package that follows solely from finite Pick
    positivity and normal-family compactness. -/
def HasMontelInterpolant : Prop :=
  ∃ H : ℂ → ℂ,
    DifferentiableOn ℂ H rightHalfPlane ∧
    IsPositiveRealOn H rightHalfPlane ∧
    ∀ i : ℕ,
      H (PickInterpolation.pickNode (i + 1) : ℂ) =
        R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)

theorem montel_interpolant_from_all_depth_positivity
    (h_pick_pos : ∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) :
    HasMontelInterpolant := by
  obtain ⟨F⟩ := finitePickFamily_of_all_depth_positivity h_pick_pos
  obtain ⟨L⟩ := schurNormalFamilyCompactness_proved F
  exact ⟨halfPlaneInterpolant L,
    halfPlaneInterpolant_differentiableOn L h_pick_pos,
    halfPlaneInterpolant_isPositiveRealOn L h_pick_pos,
    halfPlaneInterpolant_matches L h_pick_pos⟩

/-- Complete analytic data needed after the all-depth Pick positivity step.
    Constructing this package from all finite Pick matrices is precisely the
    remaining Montel/infinite-interpolation obligation. -/
def HasMontelRigidityData : Prop :=
  ∃ H : ℂ → ℂ,
    DifferentiableOn ℂ H rightHalfPlane ∧
    IsPositiveRealOn H rightHalfPlane ∧
    (∀ i : ℕ,
      H (PickInterpolation.pickNode (i + 1) : ℂ) =
        R_boundary (PickInterpolation.pickNode (i + 1) : ℂ)) ∧
    IsNevanlinnaOn (rigidityDifference H) farRightHalfPlane ∧
    MeromorphicOn R_boundary rightHalfPlane

/-- The already formalized rigidity, continuation, and pole-exclusion steps
    turn a Montel interpolant package into pole-freeness of `R_boundary`. -/
theorem R_boundary_pole_free_of_montel_data
    (hdata : HasMontelRigidityData) :
    ∀ x : ℂ, 0 < x.re → ¬ PoleExclusion.HasPoleAt R_boundary x := by
  rcases hdata with ⟨H, hH_holo, hH_pos, hH_match, hDiff_nev, hR_mer⟩
  have hDiff_zero : Set.EqOn (rigidityDifference H) 0 farRightHalfPlane :=
    rigidityDifference_eq_zero_on_farRightHalfPlane H hDiff_nev hH_match
  have hEq_far : Set.EqOn R_boundary H farRightHalfPlane := by
    intro z hz
    have hz0 := hDiff_zero hz
    exact (sub_eq_zero.mp hz0).symm
  have hH_mer : MeromorphicOn H rightHalfPlane :=
    (hH_holo.analyticOnNhd isOpen_rightHalfPlane).meromorphicOn
  have hIdentity :
      ∀ x ∈ rightHalfPlane, R_boundary =ᶠ[nhdsWithin x {x}ᶜ] H :=
    meromorphic_identity_continuation hR_mer hH_mer hEq_far
  exact R_boundary_pole_free_of_interpolant H hH_holo hH_pos hH_match hIdentity

/-- Concrete assembly of the Montel-rigidity implication.  Its sole analytic
    input is now the exact infinite-interpolation package, rather than an
    already assembled pole-freeness implication. -/
theorem montel_rigidity_from_all_depth_positivity
    (h_interpolant :
      (∀ N : ℕ, 0 < N →
        Matrix.PosDef
          (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) →
      HasMontelRigidityData) :
    (∀ N : ℕ, 0 < N →
      Matrix.PosDef
        (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) →
    ∀ x : ℂ, 0 < x.re → ¬ PoleExclusion.HasPoleAt R_boundary x := by
  intro h_pick_pos
  exact R_boundary_pole_free_of_montel_data (h_interpolant h_pick_pos)

/-- Master dependency stitch from all-depth positivity to pole exclusion. This is an assembly theorem, not a proof of the Montel/Nevanlinna step. -/
theorem pole_free_from_all_depth_positivity
    (h_pick_pos : ∀ (N : ℕ), 0 < N → Matrix.PosDef (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ))
    (h_montel_rigidity : (∀ (N : ℕ), 0 < N → Matrix.PosDef (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) → ∀ x : ℂ, 0 < x.re → ¬ PoleExclusion.HasPoleAt R_boundary x) :
    ∀ x : ℂ, 0 < x.re → ¬ PoleExclusion.HasPoleAt R_boundary x := by
  exact h_montel_rigidity h_pick_pos

end
end Rigidity
end SEERAVERSE
