import QuanIncapacity.Qutrit.RelativeEntropy
import QuanIncapacity.Qutrit.Stinespring
import QuanIncapacity.Framework.AllBlockInformation

/-! The qutrit's all-block information zeros are unconditional kernel theorems.
Each operational zero takes its corresponding external coding theorem. -/

noncomputable section
open QIT

namespace QuanIncapacity

theorem qutrit_all_block_zero_information : QutritAllBlockZeroInformation := by
  intro n _
  haveI : Nonempty (QIT.TensorPower (Fin 3) n) := tensorPower_nonempty_of_nonempty n
  constructor
  · exact (qutrit_complete_relativeEntropy_order.tensorPower n).coherent_nonpos
      (qutrit_complementary.tensorPower n)
  · intro k E
    exact (qutrit_complete_relativeEntropy_order.tensorPower n).holevo_le E

theorem qutrit_privateOneShot_zero (n : ℕ) :
    Information.privateOneShot (Λ.tensorPower n) (Λc.tensorPower n) = 0 :=
  qutrit_complete_relativeEntropy_order.privateOneShot_tensorPower_eq_zero n

theorem qutrit_coherentInformation_zero (n : ℕ) : (Λ.tensorPower n).coherentInformation = 0 :=
  qutrit_complete_relativeEntropy_order.coherentInformation_tensorPower_eq_zero qutrit_complementary n

theorem qutrit_regularizedPrivate_zero : Information.regularizedPrivate Λ Λc = 0 :=
  qutrit_complete_relativeEntropy_order.regularizedPrivate_eq_zero

theorem qutrit_regularizedCoherentInformation_zero : Λ.regularizedCoherentInformation = 0 :=
  qutrit_complete_relativeEntropy_order.regularizedCoherentInformation_eq_zero qutrit_complementary

/-- Compatibility with the original state-optimized coherent-information definition. -/
theorem qutrit_coherentInfoMax_zero : coherentInfoMax = 0 := by
  have hz : 0 ∈ {x : ℝ | ∃ ρ : State (Fin 3), coherentInfo ρ = x} := by
    obtain ⟨ψ, hψ⟩ := zero_mem_coherentInformationValues Λ
    refine ⟨ψ.state.marginalB, ?_⟩
    change Information.coherent Λ Λc ψ.state.marginalB = 0
    rw [← qutrit_complementary.coherentInformationFor_eq ψ]
    exact hψ
  have hb : ∀ x ∈ {x : ℝ | ∃ ρ : State (Fin 3), coherentInfo ρ = x}, x ≤ 0 := by
    rintro x ⟨ρ, rfl⟩
    exact qutrit_complete_relativeEntropy_order.coherent_nonpos qutrit_complementary ρ
  exact le_antisymm (csSup_le ⟨0, hz⟩ hb) (le_csSup ⟨0, hb⟩ hz)

/-- Compatibility with the original definition ranging over all finite index types. -/
theorem qutrit_privateInfoMax_zero : privateInfoMax = 0 := by
  have hz : 0 ∈ {x : ℝ | ∃ ι : Type, ∃ _ : Fintype ι,
      ∃ E : Ensemble ι (Fin 3), privateInfo E = x} := by
    obtain ⟨k, E, hE⟩ := zero_mem_privateValues Λ Λc
    exact ⟨Fin k, inferInstance, E, hE⟩
  have hb : ∀ x ∈ {x : ℝ | ∃ ι : Type, ∃ _ : Fintype ι,
      ∃ E : Ensemble ι (Fin 3), privateInfo E = x}, x ≤ 0 := by
    rintro x ⟨ι, hi, E, rfl⟩
    exact qutrit_complete_relativeEntropy_order.privateInfo_nonpos E
  exact le_antisymm (csSup_le ⟨0, hz⟩ hb) (le_csSup ⟨0, hb⟩ hz)

theorem qutrit_privateCapacity_zero (coding : External.PrivateCoding Λ Λc) :
    PrivateCoding.capacity Λ Λc = 0 :=
  qutrit_complete_relativeEntropy_order.privateCapacity_eq_zero qutrit_complementary coding

theorem qutrit_quantumCapacity_zero (coding : External.QuantumCoding Λ) : Λ.quantumCapacity = 0 :=
  qutrit_complete_relativeEntropy_order.quantumCapacity_eq_zero qutrit_complementary coding

end QuanIncapacity
