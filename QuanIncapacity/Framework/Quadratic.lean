import QuanIncapacity.Framework.MatrixSpace
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators Matrix InnerProductSpace
open QIT

namespace QuanIncapacity.MatrixSpace

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- Complex quadratic forms determine a matrix, without a Hermitian hypothesis. -/
theorem ext_quadratic {A B : CMatrix a}
    (h : ∀ x : a → ℂ, star x ⬝ᵥ (A *ᵥ x) = star x ⬝ᵥ (B *ᵥ x)) : A = B := by
  apply Matrix.toEuclideanLin.injective
  apply (ext_inner_map _ _).mp
  intro x
  have hx : ⟪x, A.toEuclideanLin x⟫_ℂ = ⟪x, B.toEuclideanLin x⟫_ℂ := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, dotProduct_comm] using h (WithLp.ofLp x)
  simpa only [← RCLike.star_def, inner_conj_symm] using congrArg (starRingEnd ℂ) hx

end QuanIncapacity.MatrixSpace
