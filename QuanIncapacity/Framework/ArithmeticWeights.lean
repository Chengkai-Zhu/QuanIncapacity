import QuanIncapacity.Framework.CompleteShadowing
import QuanIncapacity.Framework.InverseVariational

/-!
# Left/right weights and arithmetic interpolation

Adjoint preservation, rather than positivity of the shadow map, transfers the
left second-moment bound to right weights. The resulting arithmetic operators
obey the inverse comparison at every point of the closed unit interval.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT

namespace QuanIncapacity.MatrixSpace

variable {a b : Type*} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

def right (X : CMatrix a) : CMatrix (a × a) := Matrix.kronecker 1 X.transpose

theorem right_mulVec (X Y : CMatrix a) : right X *ᵥ vec Y = vec (Y * X) := by
  ext ij
  simp [right, vec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.one_apply, Matrix.mul_apply, mul_comm]

theorem right_quadratic (X Y : CMatrix a) :
    star (vec Y) ⬝ᵥ (right X *ᵥ vec Y) = (Y.conjTranspose * Y * X).trace := by
  rw [right_mulVec, ← trace_adjoint_mul, Matrix.mul_assoc]

theorem left_bound_to_right {σ : CMatrix a} {ω : CMatrix b} (J : MatrixMap a b)
    (hJ : ∀ Y, J Y.conjTranspose = (J Y).conjTranspose)
    (h : ∀ Y, ((J Y).conjTranspose * ω * J Y).trace.re ≤
      (Y.conjTranspose * σ * Y).trace.re) (Y : CMatrix a) :
    ((J Y).conjTranspose * J Y * ω).trace.re ≤
      (Y.conjTranspose * Y * σ).trace.re := by
  have hy := h Y.conjTranspose
  rw [hJ, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_cycle (J Y) ω (J Y).conjTranspose,
    Matrix.trace_mul_cycle Y σ Y.conjTranspose] at hy
  exact hy

def arithmetic (σ : CMatrix a) (t : ℝ) : CMatrix (a × a) :=
  (1 - t) • left σ + t • right σ

theorem arithmetic_quadratic (σ Y : CMatrix a) (t : ℝ) :
    quadratic (arithmetic σ t) (vec Y) =
      (1 - t) * (Y.conjTranspose * σ * Y).trace.re +
        t * (Y.conjTranspose * Y * σ).trace.re := by
  simp only [quadratic, arithmetic, Matrix.add_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, left_quadratic, right_quadratic,
    Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem arithmetic_bound {σ : CMatrix a} {ω : CMatrix b} (J : MatrixMap a b)
    (hJ : ∀ Y, J Y.conjTranspose = (J Y).conjTranspose)
    (h : ∀ Y, ((J Y).conjTranspose * ω * J Y).trace.re ≤
      (Y.conjTranspose * σ * Y).trace.re) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Y : CMatrix a) :
    quadratic (arithmetic ω t) (vec (J Y)) ≤ quadratic (arithmetic σ t) (vec Y) := by
  rw [arithmetic_quadratic, arithmetic_quadratic]
  exact add_le_add (mul_le_mul_of_nonneg_left (h Y) (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left (left_bound_to_right J hJ h Y) ht0)

theorem arithmetic_posDef {σ : CMatrix a} (hσ : σ.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (arithmetic σ t).PosDef := by
  have hl : (left σ).PosDef := hσ.kronecker Matrix.PosDef.one
  have hr : (right σ).PosDef := Matrix.PosDef.one.kronecker hσ.transpose
  by_cases ht : t = 1
  · simpa [arithmetic, ht] using hr
  · exact (hl.smul (sub_pos.mpr (lt_of_le_of_ne ht1 ht))).add_posSemidef
      (hr.posSemidef.smul ht0)

theorem arithmetic_inverse_comparison {σ : CMatrix a} {ω : CMatrix b}
    (hσ : σ.PosDef) (hω : ω.PosDef) (J : MatrixMap a b)
    (hJ : ∀ Y, J Y.conjTranspose = (J Y).conjTranspose)
    (h : ∀ Y, ((J Y).conjTranspose * ω * J Y).trace.re ≤
      (Y.conjTranspose * σ * Y).trace.re) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((arithmetic ω t)⁻¹ - rep J * (arithmetic σ t)⁻¹ * (rep J).conjTranspose).PosSemidef := by
  have hA := arithmetic_posDef hσ ht0 ht1
  have hB := arithmetic_posDef hω ht0 ht1
  apply inverse_comparison hA hB
  have hp : ((rep J).conjTranspose * arithmetic ω t * rep J).PosSemidef :=
    hB.posSemidef.conjTranspose_mul_mul_same _
  have hh := hA.isHermitian.sub hp.isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro x
  rw [Complex.nonneg_iff]
  refine ⟨?_, (hh.im_star_dotProduct_mulVec_self x).symm⟩
  have hb := arithmetic_bound J hJ h ht0 ht1 (unvec x)
  simp only [quadratic, vec_unvec, ← rep_mulVec, vec_unvec] at hb
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    Shadowing.quadratic_pullback, sub_nonneg] using hb

end QuanIncapacity.MatrixSpace
