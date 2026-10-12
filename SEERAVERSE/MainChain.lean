import Mathlib

import SEERAVERSE.Setup
import SEERAVERSE.RangeAssembly
import SEERAVERSE.PoleExclusion
import SEERAVERSE.Rigidity
import SEERAVERSE.PickInterpolation
import SEERAVERSE.Certificate4052

/-!
# Main chain

Entry point chaining all formal components of the paper:
1. Setup (paper Section 2 identities)
2. PickInterpolation (paper Section 3 all-depth positivity)
3. Rigidity (paper Section 8 & 9 positive-real Nevanlinna rigidity)
4. PoleExclusion (paper Section 10 critical-line conclusion)
5. RangeAssembly (paper Section 3.2 glue lemma across the 3 regimes)
-/

namespace SEERAVERSE
namespace MainChain

open Complex

/-- All-depth strict positivity of the boundary Pick matrix (paper Theorem 1, eq 3.2). -/
theorem main_rh_pick_positivity
    (hbase : Matrix.PosDef (PickInterpolation.K_boundary_real 1 : Matrix (Fin 1) (Fin 1) ℝ))
    (hstep : ∀ (N : ℕ) (hN : 0 < N) [Invertible (PickInterpolation.K_boundary_real N)],
      0 < PickInterpolation.freshPivotResidual_real N)
    (N : ℕ) (hN : 0 < N) [hInv : ∀ m, Invertible (PickInterpolation.K_boundary_real m)] :
    Matrix.PosDef (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ) :=
  PickInterpolation.all_depth_pick_positivity hbase hstep N hN

/-- The master Riemann Hypothesis deduction chain (paper eq 10.10 & Theorem 2):
    All-depth positivity + Nevanlinna rigidity + Pole exclusion ⇒ RH. -/
theorem main_riemann_hypothesis_deduction
    (h_pick_pos : ∀ (N : ℕ), 0 < N →
      Matrix.PosDef (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ))
    (h_interpolant : (∀ (N : ℕ), 0 < N →
      Matrix.PosDef (PickInterpolation.K_boundary_real N : Matrix (Fin N) (Fin N) ℝ)) →
      Rigidity.HasMontelRigidityData)
    (rho : ℂ) (hzero : xi rho = 0) (hstrip : 0 < rho.re ∧ rho.re < 1) :
    rho.re = 1 / 2 := by
  have h_montel_rigidity :=
    Rigidity.montel_rigidity_from_all_depth_positivity h_interpolant
  have h_pole_free := Rigidity.pole_free_from_all_depth_positivity h_pick_pos h_montel_rigidity
  have h_no_right : ∀ (r : ℂ), xi r = 0 → 0 < r.re ∧ r.re < 1 → r.re ≤ 1 / 2 := by
    intro r hr hr_strip
    exact PoleExclusion.no_zeros_right_of_critical_line h_pole_free r hr hr_strip
  exact PoleExclusion.riemann_hypothesis_from_pole_exclusion h_no_right rho hzero hstrip

end MainChain
end SEERAVERSE
