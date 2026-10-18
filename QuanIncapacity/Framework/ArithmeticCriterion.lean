import QuanIncapacity.Framework.ArithmeticMetric
import QuanIncapacity.Framework.Adjoint
import QuanIncapacity.Framework.FaithfulOutput

/-!
An unconditional, arbitrary-reference arithmetic-metric consequence of
complete shadowing. The relative-entropy and Kubo–Mori identifications remain
separate targets and are not hypotheses of this theorem.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder
open QIT QuanIncapacity.MatrixSpace

namespace QuanIncapacity.Shadowing

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem complete_arithmeticMetric_order (N : Channel a b) (M : Channel a e)
    (J : MatrixMap b e) (h : IsCompleteShadow N.map M.map J)
    (hN : (N.map 1).PosDef) (hM : (M.map 1).PosDef)
    (r : Type) [Fintype r] [DecidableEq r]
    (τ X : CMatrix (r × a)) (hτ : τ.PosDef) :
    arithmeticMetric (amp r N.map τ) (amp r N.map X) ≤
      arithmeticMetric (amp r M.map τ) (amp r M.map X) := by
  have hr : IsUnbiasedShadow (amp r N.map) (amp r M.map) (amp r J) :=
    ⟨amp_map_adjoint J h.1.map_adjoint, h.1.amp_mean_eq⟩
  have hm := arithmeticMetric_comparison (amp_posDef N hN hτ) (amp_posDef M hM hτ)
    (amp r J) hr.map_adjoint
    (completeSecondMoment_of_completeShadow h r τ hτ.posSemidef) (amp r M.map X)
  rwa [hr.reconstruct] at hm

end QuanIncapacity.Shadowing
