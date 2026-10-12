import Mathlib
import SEERAVERSE.Setup

/-!
# Pick interpolation

Definitions for the boundary-first finite Pick problem (paper §2.3, §3):

* The Pick lattice `x_i = 5/2 + 2i` for `i ≥ 1` (paper eq 2.4),
  beginning at `x_1 = 9/2` with spacing 2.
* The interpolation data `w_i = R_∂(x_i)`.
* The positive-real Pick kernel `K(i, j) = (w_i + w_j)/(z_i + z_j)`.
* The depth-`N` boundary Pick matrix `K_∂^(N)` (paper eq 3.1).
* The Schur complement / fresh-pivot residual (paper §3.1).

The all-depth strict positivity `K_∂^(N) ≻ 0` for every `N ≥ 1`
(paper eq 3.2, Theorem 1) is the main result of the paper and is
left as a future theorem (not yet proven).
-/

open Matrix

namespace PickInterpolation
noncomputable section



/-- The Pick lattice `x_i = 5/2 + 2i` for `i ≥ 1` (paper eq 2.4).
    The lattice begins at `x_1 = 9/2` and has spacing 2. -/
def pickNode (i : ℕ) : ℝ := (5 : ℝ) / 2 + 2 * i

/-- The interpolation data `w_i = R_∂(x_i)` (paper §3).
    Since `x_i > 0` and `s_i = 1 / 2 + x_i > 1`, the values `w_i` are real. -/
def w (i : ℕ) : ℂ := SEERAVERSE.R_boundary (pickNode i)

/-- The positive-real Pick kernel for data `(z_i, w_i)` (paper §3):
    `K(i, j) = (w_i + w_j) / (z_i + z_j)`. -/
def pickKernel (z w : ℕ → ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (w (i.val + 1) + w (j.val + 1)) / (z (i.val + 1) + z (j.val + 1))

/-- The depth-`N` boundary Pick matrix (paper eq 3.1):
    `K_∂^(N) = [(R_∂(x_i) + R_∂(x_j))/(x_i + x_j)]_{i,j=1}^N`. -/
def K_boundary (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  pickKernel (fun i => (pickNode i : ℂ)) w N

/-- The boundary Pick matrix is symmetric: the kernel `(w_i + w_j)/(z_i + z_j)`
    is symmetric in `i, j`. -/
theorem K_boundary_symmetric (N : ℕ) : (K_boundary N).transpose = K_boundary N := by
  ext i j
  simp [K_boundary, pickKernel, w, pickNode]
  congr 1
  <;> simp [add_comm]

/-! ## Threshold quantities (paper §3.1, eq 3.4–3.7) -/

/-- The threshold parameter `α_N` (paper eq 3.5):
    `α_N = 2(N+1)(2N+3) / (2N+5)`. -/
def alpha_N (N : ℕ) : ℝ := 2 * ((N : ℝ) + 1) * (2 * (N : ℝ) + 3) / (2 * (N : ℝ) + 5)

/-- The exponential decay term `E_N` (paper eq 3.6):
    `E_N = (4/9)^N · (log 3 / 3 + log 3 / (2N) + 1 / (4N²))`.
    Only meaningful for `N ≥ 1`. -/
def E_N (N : ℕ) : ℝ :=
  (4 / 9 : ℝ)^N * (Real.log 3 / 3 + Real.log 3 / (2 * (N : ℝ)) + 1 / (4 * (N : ℝ)^2))

/-- The gamma ratio `G_N` (paper eq 3.7):
    `G_N = Γ(N) · Γ(N + 7/2) / Γ(2N + 5/2)`.
    Only meaningful for `N ≥ 1`. -/
def G_N (N : ℕ) : ℝ :=
  (Real.Gamma (N : ℝ) * Real.Gamma ((N : ℝ) + (7 : ℝ) / 2)) /
  Real.Gamma (2 * (N : ℝ) + (5 : ℝ) / 2)

/-- The threshold `T_N` (paper eq 3.4):
    `T_N = α_N · E_N / (N⁴ · N! · G_N)`.
    Only meaningful for `N ≥ 1`. -/
def T_N (N : ℕ) : ℝ :=
  (alpha_N N * E_N N) / ((N : ℝ)^4 * (Nat.factorial N : ℝ) * G_N N)

/-- `α_N > 0` for all `N ≥ 0`. -/
theorem alpha_N_pos (N : ℕ) : 0 < alpha_N N := by
  rw [alpha_N]
  positivity

/-- `E_N > 0` for `N ≥ 1`. -/
theorem E_N_pos (N : ℕ) (hN : 0 < N) : 0 < E_N N := by
  rw [E_N]
  positivity

/-- `G_N > 0` for `N ≥ 1` (gamma function is positive on positive reals). -/
theorem G_N_pos (N : ℕ) (hN : 0 < N) : 0 < G_N N := by
  rw [G_N]
  positivity

/-- `T_N > 0` for `N ≥ 1`. -/
theorem T_N_pos (N : ℕ) (hN : 0 < N) : 0 < T_N N := by
  rw [T_N]
  apply div_pos
  · exact mul_pos (alpha_N_pos N) (E_N_pos N hN)
  · apply mul_pos
    · apply mul_pos
      · positivity
      · positivity
    · exact G_N_pos N hN

/-! ## Schur complement and block decomposition (paper §3.1) -/

/-- The off-diagonal block of `K_∂^(N+1)` (the last column, excluding the last entry).
    This is the `b_N` vector in the paper's block decomposition:
    `K_∂^(N+1) = [[K_∂^(N), b_N], [b_Nᵀ, d_N]]`. -/
def b_N_vec (N : ℕ) : Fin N → ℂ :=
  fun i => K_boundary (N + 1) (i.castSucc) (Fin.last N)

/-- The diagonal entry of `K_∂^(N+1)` (the last entry).
    This is the `d_N` scalar in the paper's block decomposition. -/
def d_N (N : ℕ) : ℂ :=
  K_boundary (N + 1) (Fin.last N) (Fin.last N)

/-- The top-left block of `K_∂^(N+1)` is `K_∂^(N)`. -/
theorem K_boundary_block_top_left (N : ℕ) (i j : Fin N) :
    K_boundary (N + 1) (i.castSucc) (j.castSucc) = K_boundary N i j := rfl

/-- The top-right block of `K_∂^(N+1)` is `b_N`. -/
theorem K_boundary_block_top_right (N : ℕ) (i : Fin N) :
    K_boundary (N + 1) (i.castSucc) (Fin.last N) = b_N_vec N i := rfl

/-- The bottom-left block of `K_∂^(N+1)` is `b_Nᵀ` (by symmetry of the Pick kernel). -/
theorem K_boundary_block_bottom_left (N : ℕ) (j : Fin N) :
    K_boundary (N + 1) (Fin.last N) (j.castSucc) = b_N_vec N j := by
  simp [b_N_vec, K_boundary, pickKernel, w, pickNode, Fin.last, Fin.castSucc]
  field_simp; ring

/-- The bottom-right block of `K_∂^(N+1)` is `d_N`. -/
theorem K_boundary_block_bottom_right (N : ℕ) :
    K_boundary (N + 1) (Fin.last N) (Fin.last N) = d_N N := rfl

/-! ## Fresh-pivot residual (Schur complement) -/

/-- The fresh-pivot residual (Schur complement) of the depth-`N+1` Pick matrix
    relative to the depth-`N` block (paper §3.1).

    This is `d_N - b_Nᵀ (K_∂^(N))⁻¹ b_N`, the Schur complement of the
    top-left block `K_∂^(N)` in `K_∂^(N+1)`.

    By the Schur-complement criterion, when `K_∂^(N) ≻ 0`, the positivity
    of `K_∂^(N+1)` is equivalent to positivity of this residual.

    The paper's quantitative bound (eq 3.3) is `r_{N,∂}^{(2)} > T_N`,
    where `r_{N,∂}^{(2)}` is a normalized form of this residual.

    Requires the `Invertible` instance for `K_∂^(N)`. -/
def freshPivotResidual (N : ℕ) [Invertible (K_boundary N)] : ℂ :=
  d_N N - ∑ i : Fin N, (b_N_vec N i) * (⅟(K_boundary N)).mulVec (b_N_vec N) i

/-! ## Positive definiteness (paper Theorem 1, eq 3.2) -/

/-- The real part of the boundary Pick matrix, for use with Mathlib's `Matrix.PosDef`.
    Since all entries of `K_boundary N` are real (the nodes and data are real),
    this is the matrix cast to `ℝ`. -/
def K_boundary_real (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.map (K_boundary N) Complex.re

/-! ### Schur complement proof machinery -/

/-- Equivalence between `Fin N ⊕ Fin 1` and `Fin (N + 1)`, mapping
     `Sum.inl i` to `i.castSucc` and `Sum.inr _` to `Fin.last N`. -/
def finN_sum_fin1_equiv (N : ℕ) : (Fin N ⊕ Fin 1) ≃ Fin (N + 1) :=
  Equiv.mk
    (Sum.elim (Fin.castSucc) (fun _ => Fin.last N))
    (fun j => if h : j.val < N then Sum.inl ⟨j.val, h⟩ else Sum.inr 0)
    (by
      intro s
      cases s with
      | inl i =>
        have h : i.castSucc.val < N := i.is_lt
        simp [ite_eq_left h, Fin.castSucc]
      | inr v =>
        have h : ¬ (Fin.last N).val < N := by simp
        have hv : v = 0 := by ext; omega
        subst hv
        simp [ite_eq_right h, Fin.last, Fin.ext_iff])
    (by
      intro j
      dsimp
      by_cases h : j.val < N
      · ext; simp [h]
      · ext
        have hN : j.val = N := by omega
        simp [h, hN])
/-- The real-valued column vector `b_N` as a `Matrix (Fin N) (Fin 1) ℝ`. -/
def b_N_vec_real (N : ℕ) : Matrix (Fin N) (Fin 1) ℝ :=
   fun i _ => (b_N_vec N i).re

/-- The real-valued scalar `d_N` as a `Matrix (Fin 1) (Fin 1) ℝ`. -/
def d_N_real (N : ℕ) : Matrix (Fin 1) (Fin 1) ℝ :=
   fun _ _ => (d_N N).re

/-- The real-valued fresh-pivot residual (Schur complement), expressed using the real matrix. -/
def freshPivotResidual_real (N : ℕ) [Invertible (K_boundary_real N)] : ℝ :=
   (d_N N).re - ∑ i : Fin N, (b_N_vec N i).re * (⅟(K_boundary_real N)).mulVec (fun j => (b_N_vec N j).re) i

/-- The submatrix of `K_boundary_real (N+1)` with respect to the block equiv
     equals the `fromBlocks` matrix. -/
theorem K_boundary_real_submatrix_eq (N : ℕ) :
     (K_boundary_real (N + 1)).submatrix (finN_sum_fin1_equiv N) (finN_sum_fin1_equiv N) =
     Matrix.fromBlocks (K_boundary_real N) (b_N_vec_real N) ((b_N_vec_real N)ᵀ) (d_N_real N) := by
   ext i j
   cases i <;> cases j <;>
   simp [finN_sum_fin1_equiv, b_N_vec_real, d_N_real, K_boundary_real, Matrix.fromBlocks, Matrix.submatrix]
   <;> try simp [K_boundary, pickKernel, w, pickNode, b_N_vec, d_N, Fin.last, Fin.castSucc]
   <;> try ring_nf
   <;> try field_simp
   <;> try simp [add_comm]

/-- A 1×1 real matrix is PosDef iff its entry is positive. -/
theorem posDef_1x1_iff_pos (a : ℝ) :
     Matrix.PosDef ((fun _ _ => a) : Matrix (Fin 1) (Fin 1) ℝ) ↔ 0 < a := by
   constructor
   · intro h
     have h1 := h.2 (x := Finsupp.single 0 1) (by simp)
     simp at h1
     exact h1
   · intro ha
     refine ⟨?_, ?_⟩
     · unfold Matrix.IsHermitian
       ext i j
       change star a = a
       simp
     · intro x hx
       have hx0 : x 0 ≠ 0 := by
         intro h0
         have : x = 0 := by
           apply Finsupp.ext
           intro i
           have hi : i = 0 := by ext; omega
           subst hi
           assumption
         contradiction
       have : x = Finsupp.single 0 (x 0) := by
         apply Finsupp.ext
         intro i
         have hi : i = 0 := by ext; omega
         subst hi
         simp
       rw [this]
       simp
       have hsq : 0 < (x 0) * (x 0) := by
         simpa [mul_comm, mul_assoc] using mul_pos (abs_pos.mpr hx0) (abs_pos.mpr hx0)
       rw [mul_comm (x 0) a, mul_assoc]
       exact mul_pos ha hsq

/-- Positive definiteness of a block matrix is equivalent to positive definiteness
     of the Schur complement (given the top-left block is PosDef). -/
theorem posDef_fromBlocks_schur₁₁ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {D : Matrix n n ℝ} (hA : A.PosDef) [Invertible A] :
     (Matrix.fromBlocks A B Bᵀ D).PosDef ↔ (D - Bᵀ * A⁻¹ * B).PosDef := by
   have hBh : Bᵀ = Bᴴ := by ext i j; simp [Matrix.star_apply, Matrix.transpose_apply]
   have hBh' : Bᴴ = Bᵀ := hBh.symm
   constructor
   · intro h
     have hPS : (D - Bᵀ * A⁻¹ * B).PosSemidef := by
       have h1 := (Matrix.PosDef.fromBlocks₁₁ B D hA).mp (by
         rw [hBh']
         exact h.posSemidef)
       rw [hBh'] at h1
       exact h1
     have hUnit : IsUnit (D - Bᵀ * A⁻¹ * B) := by
       have h_det_block : (Matrix.fromBlocks A B Bᵀ D).det ≠ 0 := by
              exact (isUnit_iff_ne_zero).mp ((isUnit_iff_isUnit_det _).mp h.isUnit)
       have h_det_A : A.det ≠ 0 := by
              exact (isUnit_iff_ne_zero).mp ((isUnit_iff_isUnit_det _).mp hA.isUnit)
       have h_det_eq : (Matrix.fromBlocks A B Bᵀ D).det = A.det * (D - Bᵀ * A⁻¹ * B).det := by
          have h_det_eq' : (Matrix.fromBlocks A B Bᵀ D).det = A.det * (D - Bᵀ * ⅟A * B).det :=
            Matrix.det_fromBlocks₁₁ A B Bᵀ D
          simpa [invOf_eq_inv] using h_det_eq'
       have h_det_schur : (D - Bᵀ * A⁻¹ * B).det ≠ 0 := by
              rw [h_det_eq] at h_det_block
              exact (mul_ne_zero_iff.mp h_det_block).2
       exact (isUnit_iff_isUnit_det _).mpr ((isUnit_iff_ne_zero).mpr h_det_schur)
     exact (hPS.posDef_iff_isUnit).2 hUnit
   · intro h
     have hPS : (Matrix.fromBlocks A B Bᵀ D).PosSemidef := by
       have h1 := (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr (by
         rw [hBh']
         exact h.posSemidef)
       rw [hBh'] at h1
       exact h1
     have hUnit : IsUnit (Matrix.fromBlocks A B Bᵀ D) := by
       have h_det_A : A.det ≠ 0 := by
              exact (isUnit_iff_ne_zero).mp ((isUnit_iff_isUnit_det _).mp hA.isUnit)
       have h_det_schur : (D - Bᵀ * A⁻¹ * B).det ≠ 0 := by
              exact (isUnit_iff_ne_zero).mp ((isUnit_iff_isUnit_det _).mp h.isUnit)
       have h_det_schur_inv : (D - Bᵀ * ⅟A * B).det ≠ 0 := by
              simpa [invOf_eq_inv] using h_det_schur
       have h_det_eq : (Matrix.fromBlocks A B Bᵀ D).det = A.det * (D - Bᵀ * ⅟A * B).det := by
              exact Matrix.det_fromBlocks₁₁ A B Bᵀ D
       have h_det_block : (Matrix.fromBlocks A B Bᵀ D).det ≠ 0 := by
              rw [h_det_eq]
              exact mul_ne_zero h_det_A h_det_schur_inv
       exact (isUnit_iff_isUnit_det _).mpr ((isUnit_iff_ne_zero).mpr h_det_block)
     exact (hPS.posDef_iff_isUnit).2 hUnit



/-- Schur complement criterion for the boundary Pick matrix (paper §3.1).
    If `K_∂^(N) ≻ 0`, then `K_∂^(N+1) ≻ 0` iff the Schur complement
    `freshPivotResidual_real N` is positive.

    This is the inductive step of the all-depth positivity proof.
    The proof uses Mathlib's `Matrix.PosSemidef.fromBlocks₁₁`
    and `Matrix.isUnit_fromBlocks_iff_of_invertible₁₁` after identifying
    `K_∂^(N+1)` with a `fromBlocks` matrix via `finN_sum_fin1_equiv`. -/
theorem schur_complement_step (N : ℕ) (hN : 0 < N)
    (hpos : Matrix.PosDef (K_boundary_real N : Matrix (Fin N) (Fin N) ℝ))
    [Invertible (K_boundary_real N)] :
    Matrix.PosDef (K_boundary_real (N + 1) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) ↔
    0 < freshPivotResidual_real N := by
  let e := finN_sum_fin1_equiv N
  let A := K_boundary_real N
  let B := b_N_vec_real N
  let D := d_N_real N
  -- Step 1: PosDef is preserved under equiv submatrix
  have hPS_equiv : (K_boundary_real (N + 1)).PosSemidef ↔ (Matrix.fromBlocks A B Bᵀ D).PosSemidef := by
    have h1 : (K_boundary_real (N + 1)).PosSemidef ↔
        ((K_boundary_real (N + 1)).submatrix e e).PosSemidef :=
      (Matrix.posSemidef_submatrix_equiv e).symm
    have h2 : ((K_boundary_real (N + 1)).submatrix e e).PosSemidef ↔
        (Matrix.fromBlocks A B Bᵀ D).PosSemidef := by
      rw [K_boundary_real_submatrix_eq N]
    exact Iff.trans h1 h2
  have hPosDef_equiv : (K_boundary_real (N + 1)).PosDef ↔ (Matrix.fromBlocks A B Bᵀ D).PosDef := by
    constructor
    · intro h
      have hPS' := hPS_equiv.mp h.posSemidef
      have hIsUnit' := (Matrix.PosSemidef.posDef_iff_isUnit h.posSemidef).mp h
      have hIsUnit'' : IsUnit (Matrix.fromBlocks A B Bᵀ D) := by
        have h3 : IsUnit (K_boundary_real (N + 1)) ↔
            IsUnit ((K_boundary_real (N + 1)).submatrix e e) :=
          (Matrix.isUnit_submatrix_equiv e e).symm
        have h4 : IsUnit ((K_boundary_real (N + 1)).submatrix e e) ↔
            IsUnit (Matrix.fromBlocks A B Bᵀ D) := by
          rw [K_boundary_real_submatrix_eq N]
        exact (Iff.trans h3 h4).mp hIsUnit'
      exact (Matrix.PosSemidef.posDef_iff_isUnit hPS').mpr hIsUnit''
    · intro h
      have hPS' := hPS_equiv.mpr h.posSemidef
      have hIsUnit' := (Matrix.PosSemidef.posDef_iff_isUnit h.posSemidef).mp h
      have hIsUnit'' : IsUnit (K_boundary_real (N + 1)) := by
        have h3 : IsUnit (K_boundary_real (N + 1)) ↔
            IsUnit ((K_boundary_real (N + 1)).submatrix e e) :=
          (Matrix.isUnit_submatrix_equiv e e).symm
        have h4 : IsUnit ((K_boundary_real (N + 1)).submatrix e e) ↔
            IsUnit (Matrix.fromBlocks A B Bᵀ D) := by
          rw [K_boundary_real_submatrix_eq N]
        exact (Iff.trans h3 h4).mpr hIsUnit'
      exact (Matrix.PosSemidef.posDef_iff_isUnit hPS').mpr hIsUnit''
  -- Step 2: Apply the Schur complement PosDef criterion
  have hSchur : (Matrix.fromBlocks A B Bᵀ D).PosDef ↔ (D - Bᵀ * A⁻¹ * B).PosDef :=
    posDef_fromBlocks_schur₁₁ hpos
  -- Step 3: The Schur complement is a 1×1 matrix, so PosDef iff entry > 0
  have hSchur_entry : (D - Bᵀ * A⁻¹ * B) 0 0 = freshPivotResidual_real N := by
    dsimp [freshPivotResidual_real, D, B, d_N_real, A]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, invOf_eq_inv]
    dsimp [b_N_vec_real]
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have h1x1 : (D - Bᵀ * A⁻¹ * B).PosDef ↔ 0 < (D - Bᵀ * A⁻¹ * B) 0 0 := by
    have hM : (D - Bᵀ * A⁻¹ * B) = (fun _ _ => (D - Bᵀ * A⁻¹ * B) 0 0) := by
      ext i j
      cases i <;> cases j <;> rfl
    rw [hM]
    exact posDef_1x1_iff_pos _
  -- Combine all equivalences
  calc (K_boundary_real (N + 1)).PosDef ↔ (Matrix.fromBlocks A B Bᵀ D).PosDef := hPosDef_equiv
    _ ↔ (D - Bᵀ * A⁻¹ * B).PosDef := hSchur
    _ ↔ 0 < (D - Bᵀ * A⁻¹ * B) 0 0 := h1x1
    _ ↔ 0 < freshPivotResidual_real N := by rw [hSchur_entry]

/-- All-depth strict positivity theorem (paper Theorem 1, eq 3.2):
    Given that the base case `K_boundary_real 1` is positive definite,
    and that the fresh-pivot residual `freshPivotResidual_real N > 0` for all `N ≥ 1`,
    the boundary Pick matrix `K_boundary_real N` is positive definite for all `N ≥ 1`.

    This is the core induction theorem assembling the all-depth positivity chain. -/
theorem all_depth_pick_positivity
    (hbase : Matrix.PosDef (K_boundary_real 1 : Matrix (Fin 1) (Fin 1) ℝ))
    (hstep : ∀ (N : ℕ) (hN : 0 < N) [Invertible (K_boundary_real N)], 0 < freshPivotResidual_real N)
    (N : ℕ) (hN : 0 < N) [hInv : ∀ m, Invertible (K_boundary_real m)] :
    Matrix.PosDef (K_boundary_real N : Matrix (Fin N) (Fin N) ℝ) := by
  induction N using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n' =>
      cases n' with
      | zero => exact hbase
      | succ k =>
        have hk : 0 < k + 1 := by omega
        have ih_k : Matrix.PosDef (K_boundary_real (k + 1)) := ih (k + 1) (by omega) hk
        haveI : Invertible (K_boundary_real (k + 1)) := hInv (k + 1)
        rw [schur_complement_step (k + 1) hk ih_k]
        exact hstep (k + 1) hk

end
end PickInterpolation
