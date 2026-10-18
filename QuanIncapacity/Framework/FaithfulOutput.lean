import QuanIncapacity.Framework.HermitianDilation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open QIT

namespace QuanIncapacity.MatrixSpace

variable {a b r : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]

/-- A positive map whose identity output is faithful preserves strict positivity. -/
theorem map_posDef_of_one (Φ : MatrixMap a b)
    (hΦ : ∀ X, X.PosSemidef → (Φ X).PosSemidef) (h1 : (Φ 1).PosDef)
    {σ : CMatrix a} (hσ : σ.PosDef) : (Φ σ).PosDef := by
  cases isEmpty_or_nonempty a with
  | inl ha =>
    letI := ha
    have heq : σ = 1 := Subsingleton.elim _ _
    simpa only [heq] using h1
  | inr ha =>
    letI := ha
    exact map_posDef_of_one_aux Φ hΦ h1 hσ
where
  map_posDef_of_one_aux [Nonempty a] (Φ : MatrixMap a b)
      (hΦ : ∀ X, X.PosSemidef → (Φ X).PosSemidef) (h1 : (Φ 1).PosDef)
      {σ : CMatrix a} (hσ : σ.PosDef) : (Φ σ).PosDef := by
    obtain ⟨c, hc, hle⟩ := (CFC.exists_pos_algebraMap_le_iff σ hσ.isHermitian).mpr
      (fun x hx ↦ hσ.isStrictlyPositive.spectrum_pos hx)
    have hdiff : (σ - c • (1 : CMatrix a)).PosSemidef := by
      simpa only [Algebra.algebraMap_eq_smul_one, Matrix.le_iff] using hle
    have hout := hΦ _ hdiff
    rw [map_sub, LinearMap.map_smul_of_tower] at hout
    simpa only [add_sub_cancel] using (h1.smul hc).add_posSemidef hout

theorem amp_one (Φ : MatrixMap a b) :
    amp r Φ 1 = Matrix.kronecker (1 : CMatrix r) (Φ 1) := by
  rw [← Matrix.one_kronecker_one]
  exact Shadowing.amp_kronecker Φ 1 1

theorem amp_posDef (N : Channel a b) (h1 : (N.map 1).PosDef)
    {σ : CMatrix (r × a)} (hσ : σ.PosDef) : (amp r N.map σ).PosDef := by
  apply map_posDef_of_one
  · exact ((Channel.idChannel r).prod N).mapsPositive
  · rw [amp_one]
    exact Matrix.PosDef.one.kronecker h1
  · exact hσ

end QuanIncapacity.MatrixSpace
