import QuanIncapacity.Activation.HelperKraus
import QuanIncapacity.Framework.ChannelMixture
import QIT.Information.Entropy.MaximallyMixed

/-! The actual receiver and the entire six-dimensional environment for
the manuscript's equiprobable binary helper ensemble. -/

noncomputable section
open QIT
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace QuanIncapacity.Helper

def input (x : Qubit) : State Q4 := (basisState x).prod (State.maximallyMixed Qubit)

theorem input_matrix (x : Qubit) : (input x).matrix =
    (Matrix.single x x (1 : ℂ)).kronecker ((1 / 2 : ℂ) • (1 : CMatrix Qubit)) := by
  rw [input, State.prod_matrix_kronecker, basisState_matrix, State.maximallyMixed_matrix]
  norm_num

def keyOutput (x : Qubit) : State Qubit :=
  State.binaryMix (1 - qH) (basisState x) (basisState (1 - x))
    (sub_nonneg.mpr qH_le_one) (by linarith [qH_nonneg])

theorem keyOutput_matrix (x : Qubit) : (keyOutput x).matrix =
    Matrix.diagonal (fun i ↦ ((if i = x then qH else 1 - qH : ℝ) : ℂ)) := by
  ext i j
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    simp [keyOutput, State.binaryMix_matrix, basisState_matrix, Matrix.single,
      Matrix.diagonal, Matrix.add_apply, Matrix.smul_apply, NNReal.smul_def,
      Real.toNNReal_of_nonneg (sub_nonneg.mpr qH_le_one),
      Real.toNNReal_of_nonneg qH_nonneg]

theorem keyOutput_entropy (x : Qubit) : (keyOutput x).vonNeumann = binaryEntropy qH := by
  rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal _ _ (keyOutput_matrix x)]
  fin_cases x <;> simp [Fin.sum_univ_two, binaryEntropy, add_comm] <;> ring

private theorem sqrt_four : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
  calc
    _ = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
    _ = 4 := by rw [sqrt_two_sq]; norm_num

set_option maxHeartbeats 1600000 in
theorem receiver_output (x : Qubit) :
    M_H.applyState (input x) = (keyOutput x).prod (State.maximallyMixed Qubit) := by
  apply State.ext
  rw [State.prod_matrix_kronecker, keyOutput_matrix, State.maximallyMixed_matrix]
  ext ⟨i, ip⟩ ⟨j, jp⟩
  change M_H_map (input x).matrix (i, ip) (j, jp) = _
  rw [input_matrix]
  fin_cases x <;> fin_cases i <;> fin_cases ip <;> fin_cases j <;> fin_cases jp <;>
    simp [M_H_map, MatrixMap.ofChoiMatrix_apply, JH, regrouped, OmegaH, tau, bellProj,
      QuanIncapacity.beta, invSqrt2, sqrt_two_inv_eq_half_sqrt, Matrix.vecMulVec,
      Matrix.kronecker, Matrix.single, Matrix.diagonal, Matrix.smul_apply, Matrix.add_apply]
  all_goals norm_num [map_ofNat]
  all_goals ring_nf
  all_goals try simp only [sqrt_two_sq, sqrt_four]
  all_goals ring

def environmentDiagonal : CMatrix (Fin 6) :=
  Matrix.diagonal fun l ↦ if l.val < 4 then (qH : ℂ) / 4 else (1 - (qH : ℂ)) / 2

set_option maxHeartbeats 2000000 in
theorem environment_output_matrix (x : Qubit) :
    (complement.applyState (input x)).matrix = environmentDiagonal := by
  ext i j
  have he := Stinespring.complementary_kraus_map kraus kraus_tracePreserving (input x).matrix i j
  change dilation.complementaryChannel.map (input x).matrix i j = _
  refine he.trans ?_
  rw [input_matrix]
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    simp [environmentDiagonal, kraus, key, shield, Matrix.diagonal, Matrix.trace,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.single,
      Matrix.smul_apply, QuanIncapacity.beta, invSqrt2, sqrt_two_inv_eq_half_sqrt,
      Complex.star_def, Complex.conj_ofReal]
  all_goals norm_num [map_ofNat]
  all_goals ring_nf
  all_goals try simp only [weightQ_square, weightE_square, alpha_square, beta_square,
    alpha_beta, beta_alpha, sqrt_two_sq]
  all_goals ring

theorem environment_output_equal (x : Qubit) :
    complement.applyState (input x) = complement.applyState (input 0) := by
  apply State.ext
  rw [environment_output_matrix, environment_output_matrix]

end QuanIncapacity.Helper
