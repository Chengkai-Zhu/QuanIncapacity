import QuanIncapacity.Framework.MatrixSpace

/-!
# General observable shadowing and its outer defect

These definitions retain arbitrary input, output, environment and reference
systems. Complete positivity is a property of the outer map into the matrix
space of observables, not positivity of the shadow map itself.
-/

noncomputable section

set_option maxHeartbeats 800000

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT
open QuanIncapacity.MatrixSpace

namespace QuanIncapacity.Shadowing

variable {a b e r : Type*}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype e] [DecidableEq e] [Fintype r] [DecidableEq r]

def variance (ρ Y : CMatrix a) : ℝ :=
  ((ρ * Y * Y).trace).re - (((ρ * Y).trace).re) ^ 2

/-- Adjoint preservation and unbiasedness, without a positivity requirement. -/
structure IsUnbiasedShadow (N : MatrixMap a b) (M : MatrixMap a e)
    (J : MatrixMap b e) : Prop where
  map_adjoint : ∀ Y, J Y.conjTranspose = (J Y).conjTranspose
  mean_eq : ∀ ρ Y, (N ρ * Y).trace = (M ρ * J Y).trace

/-- The variance condition is imposed on all finite reference systems. -/
def IsCompleteShadow (N : MatrixMap a b) (M : MatrixMap a e)
    (J : MatrixMap b e) : Prop :=
  IsUnbiasedShadow N M J ∧
  ∀ (r : Type) [Fintype r] [DecidableEq r], ∀ ρ : State (r × a),
    ∀ Y : CMatrix (r × b), Y.IsHermitian →
      variance (amp r M ρ.matrix) (amp r J Y) ≤ variance (amp r N ρ.matrix) Y

/-- Complete left second-moment comparison, including non-Hermitian operators. -/
def CompleteSecondMoment (N : MatrixMap a b) (M : MatrixMap a e)
    (J : MatrixMap b e) : Prop :=
  ∀ (r : Type) [Fintype r] [DecidableEq r], ∀ τ : CMatrix (r × a),
    τ.PosSemidef → ∀ Z : CMatrix (r × b),
      ((amp r J Z).conjTranspose * amp r M τ * amp r J Z).trace.re ≤
        (Z.conjTranspose * amp r N τ * Z).trace.re

/-- The outer defect in the row-first Hilbert–Schmidt basis. -/
def outerDefect (N : MatrixMap a b) (M : MatrixMap a e) (J : MatrixMap b e) :
    MatrixMap a (b × b) where
  toFun τ := left (N τ) - (rep J).conjTranspose * left (M τ) * rep J
  map_add' X Y := by
    simp only [map_add, left_add, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c X := by
    simp only [map_smul, left_smul, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
      RingHom.id_apply]

@[simp] theorem outerDefect_apply (N : MatrixMap a b) (M : MatrixMap a e)
    (J : MatrixMap b e) (τ : CMatrix a) :
    outerDefect N M J τ = left (N τ) - (rep J).conjTranspose * left (M τ) * rep J := rfl

omit [DecidableEq a] [DecidableEq b] in
theorem quadratic_pullback (A : CMatrix b) (T : Matrix b a ℂ) (x : a → ℂ) :
    star x ⬝ᵥ ((T.conjTranspose * A * T) *ᵥ x) =
      star (T *ᵥ x) ⬝ᵥ (A *ᵥ (T *ᵥ x)) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

/-- This identity connects the algebraic defect to actual output second moments. -/
theorem outerDefect_quadratic (N : MatrixMap a b) (M : MatrixMap a e)
    (J : MatrixMap b e) (τ : CMatrix a) (Y : CMatrix b) :
    star (vec Y) ⬝ᵥ (outerDefect N M J τ *ᵥ vec Y) =
      (Y.conjTranspose * N τ * Y).trace - ((J Y).conjTranspose * M τ * J Y).trace := by
  rw [outerDefect_apply, Matrix.sub_mulVec, dotProduct_sub, quadratic_pullback,
    rep_mulVec, left_quadratic, left_quadratic]

/-- Separate a reference block column from its vectorized observable entries. -/
def columnIndex (x : (r × b) × (r × b)) : (r × (b × b)) × r :=
  ((x.1.1, (x.1.2, x.2.2)), x.2.1)

/-- Reference amplification of the defect is repeated once per block column.
This is the matrix form of the manuscript's block-column identity. -/
theorem outerDefect_amp (N : MatrixMap a b) (M : MatrixMap a e) (J : MatrixMap b e)
    (τ : CMatrix (r × a)) :
    outerDefect (amp r N) (amp r M) (amp r J) τ =
      (Matrix.kronecker (amp r (outerDefect N M J) τ) (1 : CMatrix r)).submatrix
        columnIndex columnIndex := by
  ext ⟨⟨i, x⟩, ⟨j, y⟩⟩ ⟨⟨k, z⟩, ⟨l, w⟩⟩
  simp only [outerDefect_apply, Matrix.sub_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply, rep_amp,
    left, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.submatrix_apply, columnIndex, amp_apply, apply_ite, star_zero]
  by_cases h : j = l
  · subst l
    simp [outerDefect, left, Matrix.kronecker, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_and,
      ite_mul, mul_ite, Finset.sum_mul, Finset.mul_sum]
  · simp [h, Ne.symm h, Matrix.one_apply, ite_and,
      ite_mul, mul_ite, Finset.sum_mul, Finset.mul_sum]

theorem outerDefect_amp_posSemidef (N : MatrixMap a b) (M : MatrixMap a e)
    (J : MatrixMap b e) (hΔ : MatrixMap.IsCompletelyPositive (outerDefect N M J))
    (τ : CMatrix (r × a)) (hτ : τ.PosSemidef) :
    (outerDefect (amp r N) (amp r M) (amp r J) τ).PosSemidef := by
  rw [outerDefect_amp]
  exact ((MatrixMap.isCompletelyPositive_mapsPositive _
    (amp_completelyPositive _ hΔ) τ hτ).kronecker Matrix.PosSemidef.one).submatrix _

theorem completeSecondMoment_of_outerDefect_cp (N : MatrixMap a b) (M : MatrixMap a e)
    (J : MatrixMap b e) (hΔ : MatrixMap.IsCompletelyPositive (outerDefect N M J)) :
    CompleteSecondMoment N M J := by
  intro r _ _ τ hτ Z
  have h := (outerDefect_amp_posSemidef N M J hΔ τ hτ).dotProduct_mulVec_nonneg (vec Z)
  rw [outerDefect_quadratic] at h
  exact sub_nonneg.mp (Complex.nonneg_iff.mp h).1

def block (X : CMatrix (r × a)) (i j : r) : CMatrix a :=
  fun k l ↦ X (i, k) (j, l)

@[simp] theorem block_amp (Φ : MatrixMap a b) (X : CMatrix (r × a)) (i j : r) :
    block (amp r Φ X) i j = Φ (block X i j) := by
  ext k l
  exact amp_apply Φ X (i, k) (j, l)

omit [DecidableEq a] [DecidableEq r] in
theorem trace_mul_blocks (X Y : CMatrix (r × a)) :
    (X * Y).trace = ∑ i : r, ∑ j : r, (block X i j * block Y j i).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, block]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

theorem IsUnbiasedShadow.amp_mean_eq {N : MatrixMap a b} {M : MatrixMap a e}
    {J : MatrixMap b e} (h : IsUnbiasedShadow N M J)
    (ρ : CMatrix (r × a)) (Y : CMatrix (r × b)) :
    (amp r N ρ * Y).trace = (amp r M ρ * amp r J Y).trace := by
  simp only [trace_mul_blocks, block_amp]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact h.mean_eq _ _

theorem isCompleteShadow_of_secondMoment {N : MatrixMap a b} {M : MatrixMap a e}
    {J : MatrixMap b e} (h : IsUnbiasedShadow N M J) (h₂ : CompleteSecondMoment N M J) :
    IsCompleteShadow N M J := by
  refine ⟨h, ?_⟩
  intro r _ _ ρ Y hY
  have hJ : (amp r J Y).conjTranspose = amp r J Y := by
    rw [← amp_map_adjoint J h.map_adjoint, hY.eq]
  have hsec := h₂ r ρ.matrix ρ.pos Y
  rw [hY.eq, hJ] at hsec
  have hN : (Y * amp r N ρ.matrix * Y).trace =
      (amp r N ρ.matrix * Y * Y).trace := (Matrix.trace_mul_cycle _ _ _).symm
  have hM : (amp r J Y * amp r M ρ.matrix * amp r J Y).trace =
      (amp r M ρ.matrix * amp r J Y * amp r J Y).trace :=
        (Matrix.trace_mul_cycle _ _ _).symm
  rw [hN, hM] at hsec
  unfold variance
  rw [h.amp_mean_eq]
  exact sub_le_sub_right hsec _

theorem isCompleteShadow_of_outerDefect_cp {N : MatrixMap a b} {M : MatrixMap a e}
    {J : MatrixMap b e} (h : IsUnbiasedShadow N M J)
    (hΔ : MatrixMap.IsCompletelyPositive (outerDefect N M J)) :
    IsCompleteShadow N M J :=
  isCompleteShadow_of_secondMoment h (completeSecondMoment_of_outerDefect_cp N M J hΔ)

end QuanIncapacity.Shadowing
