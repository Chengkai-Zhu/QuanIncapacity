import QuanIncapacity.Framework.DiagonalMetric
import QuanIncapacity.Framework.Adjoint

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix
open QIT Unitary

namespace QuanIncapacity.MatrixSpace

variable {a : Type*} [Fintype a] [DecidableEq a]

def conjugation (U : Matrix.unitaryGroup a ℂ) : MatrixMap a a :=
  (conjStarAlgAut ℂ (CMatrix a) U).toAlgEquiv.toLinearEquiv.toLinearMap

theorem conjugation_apply (U : Matrix.unitaryGroup a ℂ) (X : CMatrix a) :
    conjugation U X = (U : CMatrix a) * X * (U : CMatrix a).conjTranspose := rfl

theorem conjugation_mul (U : Matrix.unitaryGroup a ℂ) (X Y : CMatrix a) :
    conjugation U (X * Y) = conjugation U X * conjugation U Y :=
  (conjStarAlgAut ℂ (CMatrix a) U).map_mul X Y

theorem conjugation_adjoint (U : Matrix.unitaryGroup a ℂ) (X : CMatrix a) :
    conjugation U X.conjTranspose = (conjugation U X).conjTranspose :=
  map_star (conjStarAlgAut ℂ (CMatrix a) U) X

theorem conjugation_trace (U : Matrix.unitaryGroup a ℂ) (X : CMatrix a) :
    (conjugation U X).trace = X.trace := by
  change ((U : CMatrix a) * X * star (U : CMatrix a)).trace = X.trace
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

theorem conjugation_inverse (U : Matrix.unitaryGroup a ℂ) (X : CMatrix a) :
    conjugation (star U) (conjugation U X) = X := by
  simp only [conjugation_apply, ← Matrix.star_eq_conjTranspose, Unitary.coe_star, star_star]
  simp only [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]

theorem conjugation_hsAdjoint (U : Matrix.unitaryGroup a ℂ) :
    hsAdjoint (conjugation U) = conjugation (star U) := by
  apply LinearMap.ext
  intro Z
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Y
  calc
    (Y * hsAdjoint (conjugation U) Z).trace =
        ((conjugation U Y.conjTranspose).conjTranspose * Z).trace := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        (hsAdjoint_pairing (conjugation U) Y.conjTranspose Z).symm
    _ = (conjugation U Y * Z).trace := by
      rw [conjugation_adjoint, Matrix.conjTranspose_conjTranspose]
    _ = (conjugation (star U) (conjugation U Y * Z)).trace :=
      (conjugation_trace (star U) _).symm
    _ = (Y * conjugation (star U) Z).trace := by
      rw [conjugation_mul, conjugation_inverse]

theorem conjugation_left_quadratic (U : Matrix.unitaryGroup a ℂ) (σ Y : CMatrix a) :
    ((conjugation U Y).conjTranspose * conjugation U σ * conjugation U Y).trace =
      (Y.conjTranspose * σ * Y).trace := by
  rw [← conjugation_adjoint, ← conjugation_mul, ← conjugation_mul, conjugation_trace]

theorem conjugation_posDef (U : Matrix.unitaryGroup a ℂ) {σ : CMatrix a}
    (hσ : σ.PosDef) : (conjugation U σ).PosDef := by
  change ((U : CMatrix a) * σ * star (U : CMatrix a)).PosDef
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (U := (U : CMatrix a)) Unitary.isUnit_coe).mpr hσ

theorem arithmeticMetric_conjugation (U : Matrix.unitaryGroup a ℂ)
    {σ : CMatrix a} (hσ : σ.PosDef) (Z : CMatrix a) :
    arithmeticMetric (conjugation U σ) (conjugation U Z) = arithmeticMetric σ Z := by
  have hcomp (V : Matrix.unitaryGroup a ℂ) (τ W : CMatrix a) (hτ : τ.PosDef) :
      arithmeticMetric τ W ≤ arithmeticMetric (conjugation V τ) (conjugation V W) := by
    have hc := arithmeticMetric_comparison hτ (conjugation_posDef V hτ) (conjugation V)
      (conjugation_adjoint V) (fun Y ↦ (congrArg Complex.re (conjugation_left_quadratic V τ Y)).le)
      (conjugation V W)
    rwa [conjugation_hsAdjoint, conjugation_inverse] at hc
  apply le_antisymm
  · simpa only [conjugation_inverse] using
      hcomp (star U) (conjugation U σ) (conjugation U Z) (conjugation_posDef U hσ)
  · exact hcomp U σ Z hσ

end QuanIncapacity.MatrixSpace
