import QuanIncapacity.Activation.HelperShields

/-! The independent four-by-four key block formula, with full shield
operators left intact. -/

noncomputable section
open QIT
open scoped Matrix BigOperators

namespace QuanIncapacity.Helper

def keyBlock (k l : Q4) : CMatrix Q4 :=
  if k = l then
    if k.1 = k.2 then (qH / 4 : ℝ) • (tau 0 + tau 1)
    else ((1 - qH) / 4 : ℝ) • (tau 2 + tau 3)
  else if (k = (0, 0) ∧ l = (1, 1)) ∨ (k = (1, 1) ∧ l = (0, 0)) then
    (qH / 4 : ℝ) • (tau 0 - tau 1)
  else if (k = (0, 1) ∧ l = (1, 0)) ∨ (k = (1, 0) ∧ l = (0, 1)) then
    ((1 - qH) / 4 : ℝ) • (tau 2 - tau 3)
  else 0

theorem Omega_key_blocks (k l p q : Q4) : OmegaH (k, p) (l, q) = keyBlock k l p q := by
  rcases k with ⟨i, j⟩
  rcases l with ⟨i', j'⟩
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    norm_num [OmegaH, keyBlock, bellProj, QuanIncapacity.beta, invSqrt2,
      Matrix.vecMulVec, Matrix.kronecker, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Complex.star_def, map_ofNat, sqrt_two_inv_mul_self]
  all_goals ring

end QuanIncapacity.Helper
