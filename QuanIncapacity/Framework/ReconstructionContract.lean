import QuanIncapacity.Framework.Adjoint

/-! Bidirectional equivalence of the trace-unbiased and actual HS-reconstruction contracts. -/
noncomputable section
open QIT QuanIncapacity.MatrixSpace

namespace QuanIncapacity.Shadowing
variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem unbiased_iff_reconstruction (N : MatrixMap a b) (M : MatrixMap a e)
    (J : MatrixMap b e) : IsUnbiasedShadow N M J ↔
      (∀ Y, J Y.conjTranspose = (J Y).conjTranspose) ∧ (hsAdjoint J).comp M = N := by
  constructor
  · intro h
    refine ⟨h.map_adjoint, ?_⟩
    apply LinearMap.ext
    intro X
    exact h.reconstruct X
  · rintro ⟨hJ, hR⟩
    refine ⟨hJ, ?_⟩
    intro X Y
    have he : hsAdjoint J (M X) = N X := congrArg (fun Φ : MatrixMap a b ↦ Φ X) hR
    have hp := hsAdjoint_pairing J Y.conjTranspose (M X)
    rw [hJ, Matrix.conjTranspose_conjTranspose, he] at hp
    simp only [Matrix.conjTranspose_conjTranspose] at hp
    rw [Matrix.trace_mul_comm, ← hp, Matrix.trace_mul_comm]

end QuanIncapacity.Shadowing
