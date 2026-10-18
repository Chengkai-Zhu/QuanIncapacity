import QuanIncapacity.Activation.HelperInformation
import QuanIncapacity.Framework.PrivateOneBlock
import QuanIncapacity.Activation.UniversalActivation
import QuanIncapacity.Qutrit.ZeroCapacity

/-! The explicit four-dimensional PPT activating partner. The helper's
quantum-capacity zero is an unconditional operational converse; only private
coding and product quantum coding are used in the activation terminal. -/

noncomputable section
open QIT

namespace QuanIncapacity.Helper

theorem privateCapacity_lower (coding : External.PrivateCoding M_H complement) :
    1 - binaryEntropy qH ≤ PrivateCoding.capacity M_H complement :=
  privateOneShot_lower.trans (Information.privateOneShot_le_capacity complementary coding)

theorem privateCapacity_pos (coding : External.PrivateCoding M_H complement) :
    0 < PrivateCoding.capacity M_H complement :=
  helper_entropy_gap_pos.trans_le (privateCapacity_lower coding)

theorem activation (privateCoding : External.PrivateCoding M_H complement)
    (quantumCoding : External.QuantumCoding (M_H.prod Λ)) :
    0 < (M_H.prod Λ).quantumCapacity :=
  Activation.universal_activation complementary (privateCapacity_pos privateCoding) quantumCoding

/-- The paper's explicit PPT superactivation terminal, including both
factors' zero quantum capacities. No helper quantum coding parameter occurs. -/
theorem superactivation (privateCoding : External.PrivateCoding M_H complement)
    (lambdaCoding : External.QuantumCoding Λ)
    (productCoding : External.QuantumCoding (M_H.prod Λ)) :
    PPT.IsChannel M_H ∧ M_H.quantumCapacity = 0 ∧ Λ.quantumCapacity = 0 ∧
      0 < (M_H.prod Λ).quantumCapacity :=
  ⟨M_H_choi_ppt, quantumCapacity_zero, qutrit_quantumCapacity_zero lambdaCoding,
    activation privateCoding productCoding⟩

end QuanIncapacity.Helper
