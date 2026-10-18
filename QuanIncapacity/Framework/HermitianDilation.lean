import QuanIncapacity.Framework.DefectEquivalence

/-!
# Hermitian dilation of arbitrary observables

A qubit reference turns any operator into a Hermitian off-diagonal block.
The input supported in the zero block has zero mean, and its variance is
exactly the desired left second moment.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT
open QuanIncapacity.MatrixSpace

namespace QuanIncapacity.Shadowing

variable {a b r s : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r]
variable [Fintype s] [DecidableEq s]

def qubitUnit (i j : Fin 2) : CMatrix (Fin 2) := Matrix.single i j 1

def zeroBlock (X : CMatrix a) : CMatrix (Fin 2 × a) :=
  Matrix.kronecker (qubitUnit 0 0) X

def hermitianDilation (Z : CMatrix a) : CMatrix (Fin 2 × a) :=
  Matrix.kronecker (qubitUnit 0 1) Z + Matrix.kronecker (qubitUnit 1 0) Z.conjTranspose

theorem hermitianDilation_isHermitian (Z : CMatrix a) :
    (hermitianDilation Z).IsHermitian := by
  unfold Matrix.IsHermitian hermitianDilation
  simp [Matrix.conjTranspose_kronecker, qubitUnit, add_comm]

theorem zeroBlock_mul_dilation (X Z : CMatrix a) :
    zeroBlock X * hermitianDilation Z = Matrix.kronecker (qubitUnit 0 1) (X * Z) := by
  simp [zeroBlock, hermitianDilation, Matrix.mul_add, ← Matrix.mul_kronecker_mul,
    qubitUnit, Matrix.single_mul_single_of_ne]

theorem zeroBlock_mul_dilation_mul_dilation (X Z : CMatrix a) :
    zeroBlock X * hermitianDilation Z * hermitianDilation Z =
      zeroBlock (X * Z * Z.conjTranspose) := by
  rw [zeroBlock_mul_dilation]
  simp [zeroBlock, hermitianDilation, Matrix.mul_add, ← Matrix.mul_kronecker_mul,
    qubitUnit, Matrix.single_mul_single_of_ne]

theorem zeroBlock_variance (X Z : CMatrix a) :
    variance (zeroBlock X) (hermitianDilation Z) = (Z.conjTranspose * X * Z).trace.re := by
  unfold variance
  rw [zeroBlock_mul_dilation_mul_dilation, zeroBlock_mul_dilation]
  change (Matrix.kronecker (qubitUnit 0 0) (X * Z * Z.conjTranspose)).trace.re -
    (Matrix.kronecker (qubitUnit 0 1) (X * Z)).trace.re ^ 2 = _
  simp only [Matrix.kronecker, Matrix.trace_kronecker]
  simp only [qubitUnit, Matrix.trace_single_eq_same,
    Matrix.trace_single_eq_of_ne (0 : Fin 2) 1 (1 : ℂ) (by decide), one_mul, zero_mul,
    Complex.zero_re, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
  exact congrArg Complex.re (Matrix.trace_mul_cycle X Z Z.conjTranspose)

theorem trace_relabel (X : CMatrix a) (f : b ≃ a) :
    (X.submatrix f f).trace = X.trace := by
  simpa only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply] using
    Equiv.sum_comp f (fun i ↦ X i i)

theorem variance_relabel (X Y : CMatrix a) (f : b ≃ a) :
    variance (X.submatrix f f) (Y.submatrix f f) = variance X Y := by
  simp only [variance, Matrix.submatrix_mul_equiv, trace_relabel]

theorem amp_kronecker (Φ : MatrixMap a b) (X : CMatrix r) (Y : CMatrix a) :
    amp r Φ (Matrix.kronecker X Y) = Matrix.kronecker X (Φ Y) := by
  ext i j
  rw [amp_apply]
  have hs : (fun k l ↦ Matrix.kronecker X Y (i.1, k) (j.1, l)) = X i.1 j.1 • Y := by
    ext k l
    rfl
  rw [hs, map_smul]
  rfl

theorem amp_reassociate (Φ : MatrixMap a b) (X : CMatrix (s × (r × a))) :
    amp (s × r) Φ (X.submatrix (Equiv.prodAssoc s r a) (Equiv.prodAssoc s r a)) =
      (amp s (amp r Φ) X).submatrix (Equiv.prodAssoc s r b) (Equiv.prodAssoc s r b) := by
  ext i j
  simp only [amp_apply, Matrix.submatrix_apply, Equiv.prodAssoc_apply]
  exact (amp_apply Φ (fun k l ↦ X (i.1.1, k) (j.1.1, l))
    (i.1.2, i.2) (j.1.2, j.2)).symm

def zeroReferenceState (ρ : State (r × a)) : State ((Fin 2 × r) × a) where
  matrix := (zeroBlock ρ.matrix).submatrix (Equiv.prodAssoc (Fin 2) r a)
    (Equiv.prodAssoc (Fin 2) r a)
  pos := ((posSemidef_single (0 : Fin 2)).kronecker ρ.pos).submatrix _
  trace_eq_one := by
    rw [trace_relabel]
    simp [zeroBlock, Matrix.trace_kronecker, qubitUnit, ρ.trace_eq_one]

def dilatedReferenceObservable (Z : CMatrix (r × a)) : CMatrix ((Fin 2 × r) × a) :=
  (hermitianDilation Z).submatrix (Equiv.prodAssoc (Fin 2) r a)
    (Equiv.prodAssoc (Fin 2) r a)

theorem dilatedReferenceObservable_isHermitian (Z : CMatrix (r × a)) :
    (dilatedReferenceObservable Z).IsHermitian :=
  (hermitianDilation_isHermitian Z).submatrix _

theorem amp_zeroReferenceState (Φ : MatrixMap a b) (ρ : State (r × a)) :
    amp (Fin 2 × r) Φ (zeroReferenceState ρ).matrix =
      (zeroBlock (amp r Φ ρ.matrix)).submatrix (Equiv.prodAssoc (Fin 2) r b)
        (Equiv.prodAssoc (Fin 2) r b) := by
  change amp (Fin 2 × r) Φ ((zeroBlock ρ.matrix).submatrix _ _) = _
  rw [amp_reassociate]
  simp only [zeroBlock, amp_kronecker]

theorem amp_dilatedReferenceObservable (Φ : MatrixMap a b)
    (hΦ : ∀ X, Φ X.conjTranspose = (Φ X).conjTranspose) (Z : CMatrix (r × a)) :
    amp (Fin 2 × r) Φ (dilatedReferenceObservable Z) =
      dilatedReferenceObservable (amp r Φ Z) := by
  unfold dilatedReferenceObservable
  rw [amp_reassociate]
  simp only [hermitianDilation, map_add, amp_kronecker, amp_map_adjoint Φ hΦ]

variable {e : Type} [Fintype e] [DecidableEq e]

theorem secondMoment_state_of_completeShadow {N : MatrixMap a b} {M : MatrixMap a e}
    {J : MatrixMap b e} (h : IsCompleteShadow N M J) (ρ : State (r × a))
    (Z : CMatrix (r × b)) :
    ((amp r J Z).conjTranspose * amp r M ρ.matrix * amp r J Z).trace.re ≤
      (Z.conjTranspose * amp r N ρ.matrix * Z).trace.re := by
  have hv := h.2 (Fin 2 × r) (zeroReferenceState ρ) (dilatedReferenceObservable Z)
    (dilatedReferenceObservable_isHermitian Z)
  rw [amp_zeroReferenceState, amp_zeroReferenceState,
    amp_dilatedReferenceObservable J h.1.map_adjoint] at hv
  change variance ((zeroBlock (amp r M ρ.matrix)).submatrix _ _)
      ((hermitianDilation (amp r J Z)).submatrix _ _) ≤
    variance ((zeroBlock (amp r N ρ.matrix)).submatrix _ _)
      ((hermitianDilation Z).submatrix _ _) at hv
  simpa only [variance_relabel, zeroBlock_variance] using hv

/-- The extra qubit recovers all complex second moments from Hermitian variances. -/
theorem completeSecondMoment_of_completeShadow {N : MatrixMap a b} {M : MatrixMap a e}
    {J : MatrixMap b e} (h : IsCompleteShadow N M J) : CompleteSecondMoment N M J := by
  intro r _ _ τ hτ Z
  by_cases hz : τ = 0
  · simp [hz]
  · have ht := State.posSemidef_trace_pos_of_ne_zero hτ hz
    have hc : 0 < τ.trace.re⁻¹ := inv_pos.mpr ht
    have hv := secondMoment_state_of_completeShadow h (State.normalizePSD τ hτ (ne_of_gt ht)) Z
    simp only [State.normalizePSD, LinearMap.map_smul_of_tower, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hv
    nlinarith

/-- All three conditions in the manuscript's variance/CP-defect proposition. -/
theorem completeShadow_iff_outerDefect_cp [Nonempty a]
    (N : Channel a b) (M : Channel a e) (J : MatrixMap b e)
    (hJ : IsUnbiasedShadow N.map M.map J) :
    IsCompleteShadow N.map M.map J ↔
      MatrixMap.IsCompletelyPositive (outerDefect N.map M.map J) :=
  ⟨fun h ↦ outerDefect_cp_of_completeSecondMoment N M J
      (completeSecondMoment_of_completeShadow h),
    isCompleteShadow_of_outerDefect_cp hJ⟩

end QuanIncapacity.Shadowing
