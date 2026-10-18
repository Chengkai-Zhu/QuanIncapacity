import QuanIncapacity.Framework.CompleteRelativeEntropy
import QIT.States.Purification.Conditioning

/-! Compression of a channel to the positive spectral support of its
identity output. All complex inputs, including off-diagonal operators,
are recovered exactly. -/

noncomputable section
open QIT
open scoped ComplexOrder MatrixOrder Matrix

namespace QuanIncapacity

variable {a b : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

theorem channel_map_adjoint (N : Channel a b) (X : CMatrix a) :
    N.map X.conjTranspose = (N.map X).conjTranspose := by
  rw [N.map_eq_ofKraus]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

namespace OutputSupport

theorem positive (N : Channel a b) : (N.map 1).PosSemidef :=
  N.mapsPositive 1 Matrix.PosSemidef.one

abbrev Space (N : Channel a b) := psdSupportIndex (N.map 1) (positive N)

def inclusion (N : Channel a b) : ReferenceIsometry (Space N) b :=
  State.psdSupportReferenceIsometry (N.map 1) (positive N)

def compression (N : Channel a b) : MatrixMap b (Space N) :=
  MatrixMap.ofKraus (fun _ : Unit ↦ (inclusion N).matrix.conjTranspose)

theorem compression_apply (N : Channel a b) (X : CMatrix b) :
    compression N X = psdSupportCompress (N.map 1) (positive N) X := by
  simp [compression, MatrixMap.ofKraus, inclusion, State.psdSupportReferenceIsometry,
    psdSupportCompress]

theorem map_supported (N : Channel a b) (X : CMatrix a) :
    Matrix.Supports (N.map X) (N.map 1) :=
  State.channel_map_supports N Matrix.PosSemidef.one
    (Matrix.Supports.of_right_posDef X 1 Matrix.PosDef.one)

def channel (N : Channel a b) : Channel a (Space N) where
  map := (compression N).comp N.map
  completelyPositive := MatrixMap.isCompletelyPositive_comp _ _
    (MatrixMap.ofKraus_completelyPositive _) N.completelyPositive
  tracePreserving X := by
    change (compression N (N.map X)).trace = X.trace
    rw [compression_apply, psdSupportCompress_trace_of_supports_right
      (positive N) (map_supported N X), N.tracePreserving]
  mapsPositive X hX := MatrixMap.ofKraus_mapsPositive _ _ (N.mapsPositive X hX)

theorem channel_map (N : Channel a b) (X : CMatrix a) :
    (channel N).map X = (inclusion N).matrix.conjTranspose * N.map X * (inclusion N).matrix := by
  rw [show (channel N).map X = compression N (N.map X) from rfl, compression_apply]
  rfl

theorem reconstruct (N : Channel a b) (X : CMatrix a) :
    (inclusion N).matrix * (channel N).map X * (inclusion N).matrix.conjTranspose = N.map X := by
  rw [show (channel N).map X = psdSupportCompress (N.map 1) (positive N) (N.map X) from
    compression_apply N (N.map X)]
  change psdSupportIsometry (N.map 1) (positive N) *
    psdSupportCompress (N.map 1) (positive N) (N.map X) *
      (psdSupportIsometry (N.map 1) (positive N)).conjTranspose = _
  apply psdSupportCompress_reconstruct_of_supports_right_and_conjTranspose (positive N)
  · exact map_supported N X
  · rw [← channel_map_adjoint]
    exact map_supported N _

theorem identity_posDef (N : Channel a b) : ((channel N).map 1).PosDef := by
  rw [show (channel N).map 1 = psdSupportCompress (N.map 1) (positive N) (N.map 1) from
    compression_apply N (N.map 1)]
  exact psdSupportCompress_self_posDef (N.map 1) (positive N)

theorem nonempty [Nonempty a] (N : Channel a b) : Nonempty (Space N) := by
  let ρ := N.applyState (State.maximallyMixed a)
  exact psdSupportIndex_nonempty_of_trace_one_supports ρ.pos (positive N)
    ρ.trace_eq_one (map_supported N _)

end OutputSupport
end QuanIncapacity
