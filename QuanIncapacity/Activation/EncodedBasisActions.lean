import QuanIncapacity.Activation.QubitRestriction
import QIT.Core.Pure

/-! Raw qutrit basis outputs used before the physical qubit decoder. -/
noncomputable section
open QIT

namespace QuanIncapacity

def e2vec : Fin 3 → ℂ := Pi.single 2 1

theorem lambda_g_projector : Λ_map (rankOneMatrix gvec) =
    (3 / 4 : ℂ) • rankOneMatrix gvec + (1 / 4 : ℂ) • rankOneMatrix e2vec := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Λ_map, rankOneMatrix, gvec, e2vec, Pi.single_apply,
      Matrix.trace, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.transpose_apply, Matrix.vecMulVec, sqrt_two_inv_eq_half_sqrt, Complex.star_def]
  all_goals ring_nf
  all_goals simp [sqrt_two_sq]
  all_goals norm_num [map_ofNat]
  all_goals ring

theorem lambda_two_projector : Λ_map (rankOneMatrix e2vec) =
    (1 / 2 : ℂ) • rankOneMatrix e2vec + (1 / 4 : ℂ) • rankOneMatrix gvec +
      (1 / 4 : ℂ) • rankOneMatrix kvec := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Λ_map, rankOneMatrix, gvec, kvec, e2vec, Pi.single_apply,
      Matrix.trace, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.transpose_apply, Matrix.vecMulVec, sqrt_two_inv_eq_half_sqrt, Complex.star_def]
  all_goals ring_nf
  all_goals simp [sqrt_two_sq]
  all_goals norm_num [map_ofNat]
  all_goals ring

theorem lambda_g_two : Λ_map (Matrix.vecMulVec gvec (star e2vec)) =
    (1 / 2 : ℂ) • Matrix.vecMulVec gvec (star e2vec) -
      (1 / 4 : ℂ) • Matrix.vecMulVec e2vec (star kvec) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Λ_map, gvec, kvec, e2vec, Pi.single_apply,
      Matrix.trace, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.transpose_apply, Matrix.vecMulVec, sqrt_two_inv_eq_half_sqrt, Complex.star_def]

  all_goals norm_num [map_ofNat]
  all_goals ring

end QuanIncapacity
