import QuanIncapacity.Framework.Shadowing
import QuanIncapacity.Framework.CompleteShadowing
import QuanIncapacity.Framework.Quadratic

/-!
# Complete observable shadowing for the actual qutrit channel

The existing scalar identity determines the entire complex outer-defect
matrix by polarization. Its established Kraus factorization can therefore
be used in the general reference-amplification theorem.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT
open QuanIncapacity.MatrixSpace

namespace QuanIncapacity

/-- The general outer defect equals the explicit qutrit component formula. -/
theorem qutrit_outerDefect_eq :
    Shadowing.outerDefect Λ_map Λc_map 𝒥_map = Δ_defect := by
  apply LinearMap.ext
  intro τ
  apply ext_quadratic
  intro x
  have h₁ := Shadowing.outerDefect_quadratic Λ_map Λc_map 𝒥_map τ (unvec x)
  have h₂ := secondMoment_eq_defect τ (unvec x)
  have hv : flat (unvec x) = x := by funext p; rfl
  rw [hv] at h₂
  calc
    _ = ((unvec x).conjTranspose * Λ_map τ * unvec x).trace -
        ((𝒥_map (unvec x)).conjTranspose * Λc_map τ * 𝒥_map (unvec x)).trace := by
      simpa only [vec_unvec] using h₁
    _ = _ := h₂

/-- The nonpositive shadow map obeys the statistical conditions for every reference. -/
theorem qutrit_complete_shadow : Shadowing.IsCompleteShadow Λ_map Λc_map 𝒥_map := by
  apply Shadowing.isCompleteShadow_of_outerDefect_cp
  · exact ⟨𝒥_adjoint_preserving, mean_agree⟩
  · rw [qutrit_outerDefect_eq, Δ_defect_eq_Δ]
    exact Δ_completelyPositive

/-- Compatibility with the original `Fin r` formulation of complete shadowing. -/
theorem qutrit_complete_shadow_map : IsCompleteShadowMap Λ_map Λc_map 𝒥_map := by
  refine ⟨𝒥_adjoint_preserving, mean_agree, ?_⟩
  intro r ρ Y hY
  have h := qutrit_complete_shadow.2 (Fin r) ρ Y hY
  have hid : (Channel.idChannel (Fin r)).map = (LinearMap.id : MatrixMap (Fin r) (Fin r)) := by
    ext X i j
    simp [Channel.idChannel, MatrixMap.ofKraus]
  simpa only [Shadowing.variance, Var, amp, hid] using h

end QuanIncapacity
