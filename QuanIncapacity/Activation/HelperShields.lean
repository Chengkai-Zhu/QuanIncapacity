import QuanIncapacity.Activation.HelperKraus

/-! Independent shield identities used in the manuscript's PPT proof. -/

noncomputable section
open QIT
open scoped Matrix BigOperators

namespace QuanIncapacity.Helper

theorem shield_sum_zero_one : tau 0 + tau 1 = (1 / 2 : ℂ) • (1 : CMatrix Q4) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tau, bellProj, QuanIncapacity.beta, invSqrt2,
      Matrix.vecMulVec, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply,
      Matrix.one_apply, sqrt_two_inv_mul_self]

theorem shield_sum_two_three : tau 2 + tau 3 =
    Matrix.single (0, 0) (0, 0) (1 : ℂ) + Matrix.single (1, 1) (1, 1) 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tau, Matrix.add_apply, Matrix.single_apply]
  all_goals ring

theorem shield_orthogonal_zero_one : tau 0 * tau 1 = 0 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tau, bellProj, QuanIncapacity.beta, invSqrt2, Matrix.vecMulVec,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.add_apply, Matrix.smul_apply,
      Matrix.single_apply, map_ofNat]
  all_goals ring

theorem shield_orthogonal_two_three : tau 2 * tau 3 = 0 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [tau, Matrix.mul_apply, Fintype.sum_prod_type]
  all_goals ring_nf
  all_goals norm_num [sqrt_two_sq]
  all_goals ring

theorem shield_transpose_zero_one : partialTransposeB (tau 0 - tau 1) =
    ((Real.sqrt 2 : ℂ)⁻¹) • (tau 2 - tau 3) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [partialTransposeB, tau, bellProj, QuanIncapacity.beta, invSqrt2,
      Matrix.vecMulVec, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.single_apply, sqrt_two_inv_eq_half_sqrt, map_ofNat]
  all_goals ring_nf
  all_goals norm_num [sqrt_two_sq]
  all_goals ring

private theorem sqrt_cube : (Real.sqrt 2 : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
  rw [pow_succ, sqrt_two_sq]

theorem shield_transpose_two_three : partialTransposeB (tau 2 - tau 3) =
    (Real.sqrt 2 : ℂ) • (tau 0 - tau 1) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [partialTransposeB, tau, bellProj, QuanIncapacity.beta, invSqrt2,
      Matrix.vecMulVec, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.single_apply, sqrt_two_inv_eq_half_sqrt, map_ofNat]
  all_goals ring_nf
  all_goals norm_num [sqrt_two_sq, sqrt_cube]
  all_goals ring

end QuanIncapacity.Helper
