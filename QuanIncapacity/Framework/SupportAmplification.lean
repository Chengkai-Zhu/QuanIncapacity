import QuanIncapacity.Framework.OutputSupport
import QuanIncapacity.Framework.IsometryRelativeEntropy
import QuanIncapacity.Framework.ChannelSimulation

/-! Support compression commutes with arbitrary finite reference systems. -/

noncomputable section
open QIT QuanIncapacity.MatrixSpace
open scoped Matrix BigOperators

namespace QuanIncapacity

variable {a b c r : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
variable [Fintype r] [DecidableEq r]

namespace IsometryCompression

def lift (r : Type) [Fintype r] [DecidableEq r] (V : ReferenceIsometry a b) :
    ReferenceIsometry (r × a) (r × b) :=
  (ReferenceIsometry.ofEquiv (Equiv.refl r)).prod V

theorem lift_matrix (V : ReferenceIsometry a b) :
    (lift r V).matrix = (1 : CMatrix r).kronecker V.matrix := by
  have hi : (ReferenceIsometry.ofEquiv (Equiv.refl r)).matrix = (1 : CMatrix r) := by
    ext i j
    rfl
  change (ReferenceIsometry.ofEquiv (Equiv.refl r)).matrix.kronecker V.matrix = _
  rw [hi]

theorem lift_channel (V : ReferenceIsometry a b) :
    Channel.ofReferenceIsometry (lift r V) =
      (Channel.idChannel r).prod (Channel.ofReferenceIsometry V) := by
  rw [lift, isometryChannel_prod, isometryChannel_refl]

theorem amp_embedding (V : ReferenceIsometry a b) (X : CMatrix (r × a)) :
    amp r (MatrixMap.ofReferenceIsometry V) X =
      (lift r V).matrix * X * (lift r V).matrix.conjTranspose := by
  have h := congrArg (fun N : Channel (r × a) (r × b) ↦ N.map X) (lift_channel (r := r) V)
  exact h.symm.trans (MatrixMap.ofReferenceIsometry_apply (lift r V) X)

theorem amp_compression (V : ReferenceIsometry a b) (X : CMatrix (r × b)) :
    amp r (map V) X = map (lift r V) X := by
  ext i j
  rw [amp_apply]
  have hl := congrFun (congrFun (map_apply V
    (Matrix.of fun k l ↦ X (i.1, k) (j.1, l))) i.2) j.2
  refine hl.trans ?_
  rw [map_apply (lift r V), lift_matrix]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite, ite_mul, mul_ite]

theorem map_adjoint (V : ReferenceIsometry a b) (X : CMatrix b) :
    map V X.conjTranspose = (map V X).conjTranspose := by
  simp only [map_apply, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end IsometryCompression

theorem amp_comp (N : MatrixMap b c) (M : MatrixMap a b) :
    amp r (N.comp M) = (amp r N).comp (amp r M) := by
  apply LinearMap.ext
  intro X
  change MatrixMap.kron (Channel.idChannel r).map (N.comp M) X =
    MatrixMap.kron (Channel.idChannel r).map N
      (MatrixMap.kron (Channel.idChannel r).map M X)
  rw [MatrixMap.kron_comp_apply_general, idChannel_map_eq, LinearMap.id_comp]

namespace OutputSupport

theorem embedding_channel (N : Channel a b) :
    (Channel.ofReferenceIsometry (inclusion N)).comp (channel N) = N := by
  apply channel_eq_of_map_eq
  apply LinearMap.ext
  intro X
  change MatrixMap.ofReferenceIsometry (inclusion N) ((channel N).map X) = N.map X
  rw [MatrixMap.ofReferenceIsometry_apply, reconstruct]

theorem amplified_output (N : Channel a b) (ρ : State (r × a)) :
    ((Channel.idChannel r).prod N).applyState ρ =
      (Channel.ofReferenceIsometry (IsometryCompression.lift r (inclusion N))).applyState
        (((Channel.idChannel r).prod (channel N)).applyState ρ) := by
  rw [IsometryCompression.lift_channel, amp_applyState_comp, embedding_channel]

theorem amplified_matrix (N : Channel a b) (X : CMatrix (r × a)) :
    amp r N.map X =
      (IsometryCompression.lift r (inclusion N)).matrix * amp r (channel N).map X *
        (IsometryCompression.lift r (inclusion N)).matrix.conjTranspose := by
  have he := congrArg Channel.map (embedding_channel N)
  change (MatrixMap.ofReferenceIsometry (inclusion N)).comp (channel N).map = N.map at he
  calc
    _ = amp r ((MatrixMap.ofReferenceIsometry (inclusion N)).comp (channel N).map) X :=
      congrArg (fun Φ : MatrixMap a b ↦ amp r Φ X) he.symm
    _ = amp r (MatrixMap.ofReferenceIsometry (inclusion N)) (amp r (channel N).map X) := by
      rw [amp_comp]
      rfl
    _ = _ := IsometryCompression.amp_embedding _ _

end OutputSupport
end QuanIncapacity
