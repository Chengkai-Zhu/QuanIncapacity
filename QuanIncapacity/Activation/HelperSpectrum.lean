import QuanIncapacity.Activation.HelperSupport
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The helper's normalized Choi state has exactly six positive eigenvalues.
Its entire environment is retained, and its Gram spectrum is derived from
the actual complementary output on the maximally mixed input. -/

noncomputable section
open QIT
open scoped Matrix BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace QuanIncapacity.Helper

theorem identity_input_sum : (1 : CMatrix Q4) =
    (2 : ℂ) • ((input 0).matrix + (input 1).matrix) := by
  rw [input_matrix, input_matrix]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Matrix.kronecker, Matrix.one_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.single_apply]

theorem environment_identity : complement.map (1 : CMatrix Q4) =
    (4 : ℂ) • environmentDiagonal := by
  rw [identity_input_sum, map_smul, map_add]
  change (2 : ℂ) • ((complement.applyState (input 0)).matrix +
    (complement.applyState (input 1)).matrix) = _
  rw [environment_output_matrix, environment_output_matrix]
  ext i j
  simp [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem kraus_gram : (ChoiGram.columns kraus).conjTranspose * ChoiGram.columns kraus =
    (4 : ℂ) • environmentDiagonal := by
  have h := ChoiGram.gram_complement kraus kraus_tracePreserving (1 : CMatrix Q4)
  have hi : (1 : CMatrix Q4).kronecker (1 : CMatrix Q4) = (1 : CMatrix (Q4 × Q4)) :=
    Matrix.one_kronecker_one
  rw [hi, Matrix.mul_one, Matrix.transpose_one] at h
  change _ = (complement.map (1 : CMatrix Q4)).transpose at h
  rw [environment_identity, Matrix.transpose_smul] at h
  simpa [environmentDiagonal] using h

theorem density_charpoly : density.charpoly = Polynomial.X ^ 10 *
    (Polynomial.X - Polynomial.C ((qH : ℂ) / 4)) ^ 4 *
      (Polynomial.X - Polynomial.C ((1 - (qH : ℂ)) / 2)) ^ 2 := by
  have hl : ChoiGram.columns kraus * ((1 / 4 : ℂ) • (ChoiGram.columns kraus).conjTranspose) =
      density := by
    rw [Matrix.mul_smul]
    exact density_gram.symm
  have hr : ((1 / 4 : ℂ) • (ChoiGram.columns kraus).conjTranspose) *
      ChoiGram.columns kraus = environmentDiagonal := by
    calc
      _ = (1 / 4 : ℂ) • ((ChoiGram.columns kraus).conjTranspose * ChoiGram.columns kraus) :=
        Matrix.smul_mul _ _ _
      _ = (1 / 4 : ℂ) • ((4 : ℂ) • environmentDiagonal) :=
        congrArg (fun D : CMatrix (Fin 6) ↦ (1 / 4 : ℂ) • D) kraus_gram
      _ = _ := by rw [smul_smul]; norm_num
  have h := Matrix.charpoly_mul_comm_of_le (ChoiGram.columns kraus)
    ((1 / 4 : ℂ) • (ChoiGram.columns kraus).conjTranspose) (by norm_num [Q4, Qubit])
  rw [hl, hr] at h
  norm_num only [Q4, Qubit, Fintype.card_prod, Fintype.card_fin, Nat.reduceSub] at h
  have hd : environmentDiagonal.charpoly =
      (Polynomial.X - Polynomial.C ((qH : ℂ) / 4)) ^ 4 *
        (Polynomial.X - Polynomial.C ((1 - (qH : ℂ)) / 2)) ^ 2 := by
    change (Matrix.diagonal (fun l : Fin 6 ↦
      if l.val < 4 then (qH : ℂ) / 4 else (1 - (qH : ℂ)) / 2)).charpoly = _
    rw [Matrix.charpoly_diagonal]
    norm_num [Fin.prod_univ_succ]
    ring
  calc
    _ = Polynomial.X ^ 10 * environmentDiagonal.charpoly := h
    _ = _ := by rw [hd]; ring

theorem environment_diagonal_nonzero (l : Fin 6) :
    (if l.val < 4 then (qH : ℂ) / 4 else (1 - (qH : ℂ)) / 2) ≠ 0 := by
  have hq : (qH : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt qH_pos
  have he : 1 - (qH : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (sub_pos.mpr qH_lt_one)
  split_ifs <;> exact div_ne_zero (by assumption) (by norm_num)

theorem environment_rank : environmentDiagonal.rank = 6 := by
  classical
  rw [environmentDiagonal, Matrix.rank_diagonal]
  simp [environment_diagonal_nonzero]

theorem density_rank : density.rank = 6 := by
  have hv : (ChoiGram.columns kraus).rank = 6 := by
    rw [← Matrix.rank_conjTranspose_mul_self, kraus_gram,
      Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero (by norm_num : (4 : ℂ) ≠ 0)), environment_rank]
  rw [density_gram, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (by norm_num : (1 / 4 : ℂ) ≠ 0)),
    Matrix.rank_self_mul_conjTranspose, hv]

end QuanIncapacity.Helper
