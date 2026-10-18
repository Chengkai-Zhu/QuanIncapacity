import QuanIncapacity.Framework.UnitaryMetric

/-!
# Spectral formula for the integrated inverse metric

The formula is valid for arbitrary faithful matrices, without a simple-spectrum
assumption. The entries of the perturbation are taken in an actual unitary
eigenbasis, so it is not a restriction to commuting perturbations.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT

namespace QuanIncapacity.MatrixSpace

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem arithmeticMetric_spectral {σ : CMatrix a} (hσ : σ.PosDef) (Z : CMatrix a) :
    arithmeticMetric σ Z =
      ∑ ij : a × a,
        BKM.inverseLogMean (hσ.isHermitian.eigenvalues ij.1) (hσ.isHermitian.eigenvalues ij.2) *
          Complex.normSq (conjugation (star hσ.isHermitian.eigenvectorUnitary) Z ij.1 ij.2) := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let D : CMatrix a := Matrix.diagonal (fun i ↦ (eig i : ℂ))
  have hD : D.PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    exact Complex.pos_iff.mpr ⟨hσ.eigenvalues_pos i, by simp⟩
  have hspec : σ = conjugation U D := hσ.isHermitian.spectral_theorem
  have hZ : conjugation U (conjugation (star U) Z) = Z := by
    simpa only [star_star] using conjugation_inverse (star U) Z
  calc
    arithmeticMetric σ Z =
        arithmeticMetric (conjugation U D) (conjugation U (conjugation (star U) Z)) := by
      rw [← hspec, hZ]
    _ = arithmeticMetric D (conjugation (star U) Z) :=
      arithmeticMetric_conjugation U hD _
    _ = _ := arithmeticMetric_diagonal eig hσ.eigenvalues_pos _

end QuanIncapacity.MatrixSpace
