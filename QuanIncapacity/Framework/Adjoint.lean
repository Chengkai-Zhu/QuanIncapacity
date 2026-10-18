import QuanIncapacity.Framework.CompleteShadowing

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT

namespace QuanIncapacity.MatrixSpace

variable {a b : Type*} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

theorem hsAdjoint_apply (J : MatrixMap a b) (Y : CMatrix b) (i j : a) :
    hsAdjoint J Y i j =
      ∑ k : b, ∑ l : b, star (J (Matrix.single i j 1) k l) * Y k l := by
  simp only [hsAdjoint, LinearMap.coe_mk, AddHom.coe_mk, unvec, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Matrix.conjTranspose_apply, rep, vec]

theorem hsAdjoint_map_adjoint (J : MatrixMap a b)
    (hJ : ∀ X, J X.conjTranspose = (J X).conjTranspose) (Y : CMatrix b) :
    hsAdjoint J Y.conjTranspose = (hsAdjoint J Y).conjTranspose := by
  ext i j
  simp only [hsAdjoint_apply, Matrix.conjTranspose_apply, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have h := congrFun (congrFun (hJ (Matrix.single i j 1)) k) l
  simp only [Matrix.conjTranspose_single, star_one, Matrix.conjTranspose_apply] at h
  rw [← h]
  exact mul_comm _ _

end QuanIncapacity.MatrixSpace

namespace QuanIncapacity.Shadowing
open QuanIncapacity.MatrixSpace

variable {a b e : Type*} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

/-- Unbiasedness is the actual Schrödinger-picture reconstruction equation. -/
theorem IsUnbiasedShadow.reconstruct {N : MatrixMap a b} {M : MatrixMap a e}
    {J : MatrixMap b e} (h : IsUnbiasedShadow N M J) (X : CMatrix a) :
    hsAdjoint J (M X) = N X := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Y
  calc
    (Y * hsAdjoint J (M X)).trace = ((J Y.conjTranspose).conjTranspose * M X).trace := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        (hsAdjoint_pairing J Y.conjTranspose (M X)).symm
    _ = (J Y * M X).trace := by rw [h.map_adjoint, Matrix.conjTranspose_conjTranspose]
    _ = (M X * J Y).trace := Matrix.trace_mul_comm _ _
    _ = (N X * Y).trace := (h.mean_eq X Y).symm
    _ = (Y * N X).trace := Matrix.trace_mul_comm _ _

end QuanIncapacity.Shadowing
