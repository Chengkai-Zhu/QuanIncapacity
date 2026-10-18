import QuanIncapacity.Activation.HelperKraus

/-! Normalized shield states and the literal Choi reconstruction formula. -/
noncomputable section
open QIT
open scoped Matrix BigOperators

namespace QuanIncapacity

theorem helper_shield_trace (j : Fin 4) : (tau j).trace = 1 := by
  fin_cases j <;>
    norm_num [tau, bellProj, beta, invSqrt2, Matrix.trace, Matrix.diag,
      sum_univ_q4, Q4, Qubit, Matrix.vecMulVec, Matrix.single_apply,
      Complex.star_def, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  all_goals ring_nf
  all_goals simp [sqrt_two_inv_sq, sqrt_two_sq]

set_option backward.isDefEq.respectTransparency false

theorem choi_reconstruction_general {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (C : CMatrix (a × b)) (X : CMatrix a) :
    MatrixMap.ofChoiMatrix C X = partialTraceA ((X.transpose.kronecker (1 : CMatrix b)) * C) := by
  ext i j
  change (∑ k : a, ∑ l : a, X k l * C (k, i) (l, j)) =
    ∑ k : a, ∑ z : a × b, (X.transpose.kronecker (1 : CMatrix b)) (k, i) z * C z (k, j)
  simp only [Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_comm (f := fun k l : a ↦ X k l * C (k, i) (l, j))

namespace Helper

def shieldState (j : Fin 4) : State Q4 where
  matrix := tau j
  pos := tau_posSemidef j
  trace_eq_one := helper_shield_trace j

theorem choi_reconstruction (X : CMatrix Q4) :
    M_H.map X = partialTraceA ((X.transpose.kronecker (1 : CMatrix Q4)) * JH) := by
  exact choi_reconstruction_general JH X

end Helper
end QuanIncapacity
