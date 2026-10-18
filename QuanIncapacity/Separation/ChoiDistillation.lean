import QuanIncapacity.Separation.SchmidtWitness
import QuanIncapacity.Framework.OneWayDistillation
import QuanIncapacity.Qutrit.ZeroCapacity

noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity

private theorem sqrt_three_inv_square : ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 = (1 / 3 : ℂ) := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem qutrit_maxEnt_matrix :
    (PureVector.maximallyEntangled (Equiv.refl (Fin 3))).state.matrix = Phi3 := by
  ext p q
  simp [PureVector.state_matrix_apply, PureVector.maximallyEntangled_amp, Phi3]
  split_ifs <;> simp_all
  rw [← pow_two, sqrt_three_inv_square]
  norm_num

theorem qutritChoiState_eq_channelOutput :
    qutritChoiState = ForwardAssistance.choiState Λ := by
  apply State.ext
  change omega = MatrixMap.kron (Channel.idChannel (Fin 3)).map Λ.map
    (PureVector.maximallyEntangled (Equiv.refl (Fin 3))).state.matrix
  rw [qutrit_maxEnt_matrix]
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Λ, Λ_map, Phi3, omega, Pminus, swap3, Matrix.trace,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]

/-- Positive two-way operational distillable entanglement, conditional only
on the external Schmidt-rank-two criterion. -/
theorem qutritChoi_twoWay_distillable (criterion : External.SchmidtRankTwoDistillation) :
    0 < Distillation.capacity qutritChoiState := by
  apply criterion (Fin 3) (Fin 3) qutritChoiState SchmidtWitness.vector
  · change SchmidtWitness.coefficient.rank ≤ 2
    rw [SchmidtWitness.coefficient_rank]
  · exact SchmidtWitness.expectation_negative

/-- The one-way distillable entanglement vanishes. The conversion from Choi
distillation to actual forward-assisted generation is proved in the repo. -/
theorem qutritChoi_oneWay_zero
    (forward : External.ForwardClassicalNoIncreaseQuantumCapacity Λ)
    (coding : External.QuantumCoding Λ) : Distillation.oneWayCapacity qutritChoiState = 0 := by
  rw [qutritChoiState_eq_channelOutput]
  exact Distillation.oneWayCapacity_eq_zero Λ forward (qutrit_quantumCapacity_zero coding)

end QuanIncapacity
