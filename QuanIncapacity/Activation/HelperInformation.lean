import QuanIncapacity.Activation.HelperOutputs
import QuanIncapacity.Framework.PrivateOptimization
import QuanIncapacity.Framework.PPTCapacity

/-! Exact private information of the specified helper ensemble, using the
actual channel and its certified full complementary environment. -/

noncomputable section
open QIT
open scoped Matrix BigOperators NNReal

namespace QuanIncapacity.Helper

def ensemble : QIT.Ensemble Qubit Q4 := uniformEnsemble Qubit input

private theorem log_two : log2 2 = 1 := by
  unfold log2
  exact div_self (ne_of_gt (Real.log_pos one_lt_two))

theorem qubit_mixed_entropy : (State.maximallyMixed Qubit).vonNeumann = 1 := by
  rw [State.vonNeumann_maximallyMixed]
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using log_two

theorem receiver_entropy (x : Qubit) : (M_H.applyState (input x)).vonNeumann =
    1 + binaryEntropy qH := by
  rw [receiver_output, State.vonNeumann_prod, keyOutput_entropy, qubit_mixed_entropy]
  ring

theorem receiver_average : (Ensemble.mapChannel M_H ensemble).averageState =
    (State.maximallyMixed Qubit).prod (State.maximallyMixed Qubit) := by
  apply State.ext
  rw [QIT.Ensemble.averageState_matrix, State.prod_matrix_kronecker]
  change (∑ x : Qubit, (ensemble.probs x) • (M_H.applyState (input x)).matrix) = _
  simp_rw [receiver_output, State.prod_matrix_kronecker, keyOutput_matrix]
  rw [State.maximallyMixed_matrix]
  ext ⟨i, ip⟩ ⟨j, jp⟩
  fin_cases i <;> fin_cases ip <;> fin_cases j <;> fin_cases jp <;>
    simp [ensemble, uniformEnsemble, uniformProbs, Fin.sum_univ_two,
      Matrix.kronecker, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal,
      NNReal.smul_def, Complex.real_smul]
  all_goals ring

theorem receiver_holevo : (Ensemble.mapChannel M_H ensemble).holevoInformation =
    1 - binaryEntropy qH := by
  rw [QIT.Ensemble.holevoInformation_def, receiver_average, State.vonNeumann_prod,
    qubit_mixed_entropy]
  change 1 + 1 - ∑ x : Qubit, (ensemble.probs x : ℝ) * (M_H.applyState (input x)).vonNeumann = _
  simp_rw [receiver_entropy]
  simp [ensemble, uniformEnsemble, uniformProbs, Fin.sum_univ_two]

theorem environment_holevo : (Ensemble.mapChannel complement ensemble).holevoInformation = 0 := by
  let E := Ensemble.mapChannel complement ensemble
  have hc : ∀ x, E.states x = complement.applyState (input 0) := environment_output_equal
  rw [QIT.Ensemble.holevoInformation_def, QIT.Ensemble.averageState_of_constant E _ hc]
  change (complement.applyState (input 0)).vonNeumann -
    ∑ x : Qubit, (ensemble.probs x : ℝ) * (complement.applyState (input x)).vonNeumann = 0
  simp_rw [environment_output_equal]
  simp [ensemble, uniformEnsemble, uniformProbs, Fin.sum_univ_two]

theorem privateInfo_eq : Information.privateInfo M_H complement ensemble = 1 - binaryEntropy qH := by
  rw [Information.privateInfo, receiver_holevo, environment_holevo, sub_zero]

theorem privateOneShot_lower : 1 - binaryEntropy qH ≤ Information.privateOneShot M_H complement := by
  rw [← privateInfo_eq]
  exact Information.privateInfo_le_oneShot M_H complement ensemble

theorem privateOneShot_pos : 0 < Information.privateOneShot M_H complement :=
  helper_entropy_gap_pos.trans_le privateOneShot_lower

theorem quantumCapacity_zero : M_H.quantumCapacity = 0 :=
  PPT.quantumCapacity_eq_zero M_H_choi_ppt

end QuanIncapacity.Helper
