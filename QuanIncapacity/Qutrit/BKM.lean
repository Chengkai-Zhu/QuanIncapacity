import QuanIncapacity.Framework.BKMCriterion
import QuanIncapacity.Qutrit.ArithmeticMetric

noncomputable section
open scoped ComplexOrder MatrixOrder
open QIT QuanIncapacity.MatrixSpace

namespace QuanIncapacity

theorem qutrit_complete_bkm_order
    (r : Type) [Fintype r] [DecidableEq r]
    (τ X : CMatrix (r × Fin 3)) (hτ : τ.PosDef) :
    BKM.metric (amp_posDef Λ qutrit_identity_output_posDef hτ) (amp r Λ_map X) ≤
      BKM.metric (amp_posDef Λc qutrit_environment_identity_output_posDef hτ) (amp r Λc_map X) :=
  Shadowing.complete_bkm_order Λ Λc 𝒥_map qutrit_complete_shadow
    qutrit_identity_output_posDef qutrit_environment_identity_output_posDef r τ X hτ

end QuanIncapacity
