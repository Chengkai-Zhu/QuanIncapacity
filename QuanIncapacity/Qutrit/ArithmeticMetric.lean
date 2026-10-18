import QuanIncapacity.Qutrit.CompleteShadow
import QuanIncapacity.Framework.ArithmeticCriterion

noncomputable section
open scoped ComplexOrder MatrixOrder
open QIT QuanIncapacity.MatrixSpace

namespace QuanIncapacity

theorem qutrit_identity_output_posDef : (Λ.map 1).PosDef := by
  change (Λ_map 1).PosDef
  rw [Λ_one]
  exact Matrix.PosDef.one

theorem qutrit_environment_identity_output_posDef : (Λc.map 1).PosDef := by
  change (Λc_map 1).PosDef
  rw [Λc_one]
  change (Matrix.diagonal (fun i : Fin 4 ↦
    if i = 0 then (3 / 2 : ℂ) else (1 / 2 : ℂ))).PosDef
  rw [Matrix.posDef_diagonal_iff]
  intro i
  by_cases hi : i = 0 <;> simp [hi] <;> norm_num

/-- The actual complementary channel dominates every amplified arithmetic
metric at every faithful input, for arbitrary complex perturbations. -/
theorem qutrit_complete_arithmeticMetric_order
    (r : Type) [Fintype r] [DecidableEq r]
    (τ X : CMatrix (r × Fin 3)) (hτ : τ.PosDef) :
    arithmeticMetric (amp r Λ_map τ) (amp r Λ_map X) ≤
      arithmeticMetric (amp r Λc_map τ) (amp r Λc_map X) :=
  Shadowing.complete_arithmeticMetric_order Λ Λc 𝒥_map qutrit_complete_shadow
    qutrit_identity_output_posDef qutrit_environment_identity_output_posDef r τ X hτ

end QuanIncapacity
