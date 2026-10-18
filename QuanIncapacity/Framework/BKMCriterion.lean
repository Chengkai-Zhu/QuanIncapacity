import QuanIncapacity.Framework.KuboMoriIntegral

noncomputable section
open scoped ComplexOrder MatrixOrder
open QIT QuanIncapacity.MatrixSpace

namespace QuanIncapacity.Shadowing

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

/-- Complete shadowing implies the complete BKM metric comparison.
The stronger complex-perturbation statement includes every traceless
Hermitian perturbation required by the manuscript. -/
theorem complete_bkm_order (N : Channel a b) (M : Channel a e)
    (J : MatrixMap b e) (h : IsCompleteShadow N.map M.map J)
    (hN : (N.map 1).PosDef) (hM : (M.map 1).PosDef)
    (r : Type) [Fintype r] [DecidableEq r]
    (τ X : CMatrix (r × a)) (hτ : τ.PosDef) :
    BKM.metric (amp_posDef N hN hτ) (amp r N.map X) ≤
      BKM.metric (amp_posDef M hM hτ) (amp r M.map X) := by
  rw [BKM.metric_eq_arithmeticMetric, BKM.metric_eq_arithmeticMetric]
  exact complete_arithmeticMetric_order N M J h hN hM r τ X hτ

end QuanIncapacity.Shadowing
