import QuanIncapacity.Framework.CompleteRelativeEntropy
import QuanIncapacity.Qutrit.BKM

/-! Complete relative-entropy domination by the actual four-dimensional environment. -/

noncomputable section
open QIT

namespace QuanIncapacity

theorem qutrit_complete_relativeEntropy_order : CompleteRelativeEntropyOrder Λ Λc :=
  Shadowing.complete_relativeEntropy_order Λ Λc 𝒥_map qutrit_complete_shadow
    qutrit_identity_output_posDef qutrit_environment_identity_output_posDef

end QuanIncapacity
