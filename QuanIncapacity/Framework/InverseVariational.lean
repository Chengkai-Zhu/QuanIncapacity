import QuanIncapacity.Framework.MatrixSpace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive inverse variational formula

All vectors are complex and the pairing is the actual Hilbert–Schmidt
coordinate pairing. Strict positivity supplies the inverse and unique
maximizer; the inverse comparison requires no positivity of the map `T`.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix
open QIT

namespace QuanIncapacity.MatrixSpace

variable {a b : Type*} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

def quadratic (A : CMatrix a) (x : a → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ x)).re

theorem quadratic_nonneg {A : CMatrix a} (hA : A.PosSemidef) (x : a → ℂ) :
    0 ≤ quadratic A x :=
  (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

theorem inverse_complete_square {A : CMatrix a} (hA : A.PosDef) (y z : a → ℂ) :
    2 * (star y ⬝ᵥ z).re - quadratic A y =
      quadratic A⁻¹ z - quadratic A (y - A⁻¹ *ᵥ z) := by
  letI := hA.isUnit.invertible
  have hAz : A *ᵥ (A⁻¹ *ᵥ z) = z := by
    simp [Matrix.mulVec_mulVec]
  have hc := congrArg Complex.re (hA.isHermitian.star_dotProduct_mulVec_comm y (A⁻¹ *ᵥ z))
  have hz := congrArg Complex.re (Matrix.star_dotProduct (A⁻¹ *ᵥ z) z)
  simp only [hAz, RCLike.star_def, Complex.conj_re] at hc hz
  simp only [quadratic, star_sub, Matrix.mulVec_sub, hAz, sub_dotProduct,
    dotProduct_sub, Complex.sub_re]
  unfold quadratic at *
  linarith

theorem inverse_variational_le {A : CMatrix a} (hA : A.PosDef) (y z : a → ℂ) :
    2 * (star y ⬝ᵥ z).re - quadratic A y ≤ quadratic A⁻¹ z := by
  rw [inverse_complete_square hA]
  exact sub_le_self _ (quadratic_nonneg hA.posSemidef _)

theorem inverse_variational_attained {A : CMatrix a} (hA : A.PosDef) (z : a → ℂ) :
    2 * (star (A⁻¹ *ᵥ z) ⬝ᵥ z).re - quadratic A (A⁻¹ *ᵥ z) = quadratic A⁻¹ z := by
  rw [inverse_complete_square hA]
  simp [quadratic]

theorem quadratic_eq_zero_iff {A : CMatrix a} (hA : A.PosDef) (x : a → ℂ) :
    quadratic A x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hp := (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos hx)).1
    change 0 < quadratic A x at hp
    linarith
  · rintro rfl
    simp [quadratic]

theorem inverse_variational_eq_iff {A : CMatrix a} (hA : A.PosDef) (y z : a → ℂ) :
    2 * (star y ⬝ᵥ z).re - quadratic A y = quadratic A⁻¹ z ↔ y = A⁻¹ *ᵥ z := by
  rw [inverse_complete_square hA]
  constructor
  · intro h
    exact sub_eq_zero.mp ((quadratic_eq_zero_iff hA _).mp (by linarith))
  · rintro rfl
    simp [quadratic]

theorem inverse_variational_sup {A : CMatrix a} (hA : A.PosDef) (z : a → ℂ) :
    sSup (Set.range (fun y : a → ℂ ↦ 2 * (star y ⬝ᵥ z).re - quadratic A y)) =
      quadratic A⁻¹ z := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨y, rfl⟩
    exact inverse_variational_le hA y z
  · apply le_csSup
    · exact ⟨quadratic A⁻¹ z, fun _ ⟨y, hy⟩ ↦ hy ▸ inverse_variational_le hA y z⟩
    · exact ⟨A⁻¹ *ᵥ z, inverse_variational_attained hA z⟩

/-- Inverse transfer, valid for every rectangular complex operator. -/
theorem inverse_comparison {A : CMatrix a} {B : CMatrix b}
    (hA : A.PosDef) (hB : B.PosDef) (T : Matrix b a ℂ)
    (h : (A - T.conjTranspose * B * T).PosSemidef) :
    (B⁻¹ - T * A⁻¹ * T.conjTranspose).PosSemidef := by
  letI := hA.isUnit.invertible
  letI := hB.isUnit.invertible
  letI := hB.inv.isUnit.invertible
  have hblock : (Matrix.fromBlocks A T.conjTranspose T.conjTranspose.conjTranspose B⁻¹).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ A T.conjTranspose hB.inv).mpr
    simpa only [Matrix.conjTranspose_conjTranspose,
      Matrix.nonsing_inv_nonsing_inv B (Matrix.isUnit_det_of_invertible B)] using h
  have hf := (Matrix.PosDef.fromBlocks₁₁ T.conjTranspose B⁻¹ hA).mp hblock
  simpa only [Matrix.conjTranspose_conjTranspose] using hf

end QuanIncapacity.MatrixSpace
