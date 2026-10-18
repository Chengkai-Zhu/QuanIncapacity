import QuanIncapacity.Qutrit.AlgebraicConsequences
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! The outer-defect Choi matrix is `8/9` times an orthogonal projector of
rank three, with a 24-dimensional kernel. All matrices use input-first Choi
ordering, as in Lean-QIT. -/

noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.DefectSpectrum

abbrev Space := Fin 3 × (Fin 3 × Fin 3)

def columns : Matrix Space (Fin 3) ℂ := Matrix.of fun p μ ↦ (1 / 2 : ℂ) * G μ p.2 p.1

set_option maxHeartbeats 800000 in
theorem columns_orthonormal : columns.conjTranspose * columns = 1 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;>
    norm_num [columns, G, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, map_ofNat]

def projector : CMatrix Space := columns * columns.conjTranspose

theorem projector_hermitian : projector.IsHermitian := by
  unfold projector
  exact Matrix.isHermitian_mul_conjTranspose_self _

theorem projector_square : projector * projector = projector := by
  unfold projector
  calc
    _ = columns * (columns.conjTranspose * columns) * columns.conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [columns_orthonormal, Matrix.mul_one]

theorem projector_columns : projector * columns = columns := by
  unfold projector
  rw [Matrix.mul_assoc, columns_orthonormal, Matrix.mul_one]

theorem choi_eq : MatrixMap.choi Δ = (8 / 9 : ℂ) • projector := by
  change MatrixMap.choi (((2 / 9 : ℝ) : ℂ) • MatrixMap.ofKraus G) = _
  have hc : MatrixMap.choi (((2 / 9 : ℝ) : ℂ) • MatrixMap.ofKraus G) =
      ((2 / 9 : ℝ) : ℂ) • MatrixMap.choi (MatrixMap.ofKraus G) := rfl
  rw [hc, MatrixMap.choi_ofKraus]
  ext p q
  simp [projector, columns, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec, Matrix.smul_apply, Finset.mul_sum]
  ring

theorem columns_rank : columns.rank = 3 := by
  have hlo := Matrix.rank_mul_le_right columns.conjTranspose columns
  rw [columns_orthonormal, Matrix.rank_one] at hlo
  have hhi := Matrix.rank_le_card_width columns
  norm_num at hlo hhi
  exact le_antisymm hhi hlo

theorem projector_rank : projector.rank = 3 := by
  have hlo := Matrix.rank_mul_le_left projector columns
  rw [projector_columns, columns_rank] at hlo
  have hhi := Matrix.rank_mul_le_left columns columns.conjTranspose
  rw [columns_rank] at hhi
  exact le_antisymm hhi hlo

theorem choi_rank : (MatrixMap.choi Δ).rank = 3 := by
  rw [choi_eq, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (by norm_num : (8 / 9 : ℂ) ≠ 0)), projector_rank]

theorem choi_polynomial : MatrixMap.choi Δ * MatrixMap.choi Δ =
    (8 / 9 : ℂ) • MatrixMap.choi Δ := by
  rw [choi_eq, Matrix.smul_mul, Matrix.mul_smul, projector_square, smul_smul]

theorem choi_columns : MatrixMap.choi Δ * columns = (8 / 9 : ℂ) • columns := by
  rw [choi_eq, Matrix.smul_mul, projector_columns]

theorem choi_kernel_iff (x : Space → ℂ) :
    MatrixMap.choi Δ *ᵥ x = 0 ↔ columns.conjTranspose *ᵥ x = 0 := by
  rw [choi_eq, Matrix.smul_mulVec]
  have h : (8 / 9 : ℂ) ≠ 0 := by norm_num
  constructor
  · intro hx
    have hp : projector *ᵥ x = 0 := (smul_eq_zero.mp hx).resolve_left h
    have hh := congrArg (fun v ↦ columns.conjTranspose *ᵥ v) hp
    simp only [projector, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      columns_orthonormal, Matrix.one_mul, Matrix.mulVec_zero] at hh
    exact hh
  · intro hx
    simp only [projector, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero, smul_zero]

theorem choi_kernel_finrank :
    Module.finrank ℂ (MatrixMap.choi Δ).mulVecLin.ker = 24 := by
  have h := LinearMap.finrank_range_add_finrank_ker (MatrixMap.choi Δ).mulVecLin
  change (MatrixMap.choi Δ).rank +
    Module.finrank ℂ (MatrixMap.choi Δ).mulVecLin.ker = Module.finrank ℂ (Space → ℂ) at h
  rw [choi_rank, Module.finrank_pi] at h
  norm_num [Space] at h
  omega

theorem choi_charpoly : (MatrixMap.choi Δ).charpoly =
    Polynomial.X ^ 24 * (Polynomial.X - Polynomial.C (8 / 9 : ℂ)) ^ 3 := by
  have h := Matrix.charpoly_mul_comm_of_le columns ((8 / 9 : ℂ) • columns.conjTranspose)
    (by norm_num [Space])
  rw [Matrix.mul_smul, Matrix.smul_mul, columns_orthonormal] at h
  change ((8 / 9 : ℂ) • projector).charpoly = _ at h
  rw [← choi_eq] at h
  have hd : (8 / 9 : ℂ) • (1 : CMatrix (Fin 3)) = Matrix.diagonal (fun _ ↦ (8 / 9 : ℂ)) := by
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal, mul_ite]
  rw [hd, Matrix.charpoly_diagonal] at h
  simpa [Space, Fin.prod_univ_succ, pow_succ] using h

theorem choi_roots (z : ℂ) : Polynomial.IsRoot (MatrixMap.choi Δ).charpoly z ↔
    z = 0 ∨ z = (8 / 9 : ℂ) := by
  simp [choi_charpoly, Polynomial.IsRoot, mul_eq_zero, sub_eq_zero]

end QuanIncapacity.DefectSpectrum
