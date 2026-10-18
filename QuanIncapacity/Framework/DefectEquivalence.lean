import QuanIncapacity.Framework.CompleteShadowing

/-!
# Converse direction of the complete second-moment certificate

Arbitrary operators, including their complex cross terms, are essential.
Testing a single reference block column recovers the Choi positivity test.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT
open QuanIncapacity.MatrixSpace

namespace QuanIncapacity.Shadowing

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem outerDefect_hermitian (N : Channel a b) (M : Channel a e)
    (J : MatrixMap b e) (τ : CMatrix a) (hτ : τ.PosSemidef) :
    (outerDefect N.map M.map J τ).IsHermitian := by
  have hN : (left (N.map τ)).PosSemidef :=
    (N.mapsPositive τ hτ).kronecker Matrix.PosSemidef.one
  have hM : (left (M.map τ)).PosSemidef :=
    (M.mapsPositive τ hτ).kronecker Matrix.PosSemidef.one
  exact hN.isHermitian.sub (hM.conjTranspose_mul_mul_same (rep J)).isHermitian

theorem amp_choi_id (Φ : MatrixMap a b) :
    amp a Φ (MatrixMap.choi (LinearMap.id : MatrixMap a a)) = MatrixMap.choi Φ := by
  ext x y
  rw [amp_apply]
  have hs : (fun i j ↦ MatrixMap.choi (LinearMap.id : MatrixMap a a)
      (x.1, i) (y.1, j)) = Matrix.single x.1 y.1 (1 : ℂ) := rfl
  rw [hs]
  rfl

theorem outerDefect_cp_of_completeSecondMoment [Nonempty a]
    (N : Channel a b) (M : Channel a e) (J : MatrixMap b e)
    (h : CompleteSecondMoment N.map M.map J) :
    MatrixMap.IsCompletelyPositive (outerDefect N.map M.map J) := by
  let τ := MatrixMap.choi (LinearMap.id : MatrixMap a a)
  have hτ : τ.PosSemidef := MatrixMap.choi_id_posSemidef
  have hh : (outerDefect (amp a N.map) (amp a M.map) (amp a J) τ).IsHermitian :=
    outerDefect_hermitian ((Channel.idChannel a).prod N) ((Channel.idChannel a).prod M)
      (amp a J) τ hτ
  have hp : (outerDefect (amp a N.map) (amp a M.map) (amp a J) τ).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
    intro x
    apply Complex.nonneg_iff.mpr
    refine ⟨?_, (hh.im_star_dotProduct_mulVec_self x).symm⟩
    have hx := outerDefect_quadratic (amp a N.map) (amp a M.map) (amp a J) τ (unvec x)
    rw [vec_unvec] at hx
    rw [hx, Complex.sub_re]
    exact sub_nonneg.mpr (h a τ hτ (unvec x))
  let t : a := Classical.choice inferInstance
  let f : a × (b × b) → (a × b) × (a × b) :=
    fun x ↦ ((x.1, x.2.1), (t, x.2.2))
  have hsub := hp.submatrix f
  rw [outerDefect_amp] at hsub
  have heq :
      ((Matrix.kronecker (amp a (outerDefect N.map M.map J) τ) (1 : CMatrix a)).submatrix
        columnIndex columnIndex).submatrix f f = amp a (outerDefect N.map M.map J) τ := by
    ext x y
    simp [Matrix.submatrix_apply, columnIndex, f, Matrix.kronecker]
  rw [heq] at hsub
  change (MatrixMap.choi (outerDefect N.map M.map J)).PosSemidef
  simpa only [τ, amp_choi_id] using hsub

/-- General equivalence of the paper's conditions (ii) and (iii). -/
theorem completeSecondMoment_iff_outerDefect_cp [Nonempty a]
    (N : Channel a b) (M : Channel a e) (J : MatrixMap b e) :
    CompleteSecondMoment N.map M.map J ↔
      MatrixMap.IsCompletelyPositive (outerDefect N.map M.map J) :=
  ⟨outerDefect_cp_of_completeSecondMoment N M J,
    completeSecondMoment_of_outerDefect_cp N.map M.map J⟩

end QuanIncapacity.Shadowing
