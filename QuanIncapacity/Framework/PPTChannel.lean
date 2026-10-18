import QuanIncapacity.Framework.ComplementaryTensor
import QIT.Entanglement.PPT

/-! Complete copositivity of channels and PPT preservation under actual
receiver processing and arbitrary channel tensor powers. -/

noncomputable section
open QIT QuanIncapacity.MatrixSpace
open scoped Matrix ComplexOrder MatrixOrder

namespace QuanIncapacity.PPT

variable {a b c d r : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
variable [Fintype d] [DecidableEq d] [Fintype r] [DecidableEq r]

def transposeMap : MatrixMap a a where
  toFun X := X.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def IsChannel (N : Channel a b) : Prop :=
  (partialTransposeB (MatrixMap.choi N.map)).PosSemidef

theorem transpose_choi (N : Channel a b) :
    MatrixMap.choi ((transposeMap (a := b)).comp N.map) =
      partialTransposeB (MatrixMap.choi N.map) := by
  ext i j
  rfl

def transposedChannel (N : Channel a b) (hN : IsChannel N) : Channel a b where
  map := (transposeMap (a := b)).comp N.map
  completelyPositive := by
    change (MatrixMap.choi ((transposeMap (a := b)).comp N.map)).PosSemidef
    rw [transpose_choi]
    exact hN
  tracePreserving X := by
    change (N.map X).transpose.trace = X.trace
    rw [Matrix.trace_transpose, N.tracePreserving]
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ (by
    change (MatrixMap.choi ((transposeMap (a := b)).comp N.map)).PosSemidef
    rw [transpose_choi]
    exact hN)

def conjugateMap (N : Channel a b) : MatrixMap a b :=
  (transposeMap (a := b)).comp (N.map.comp (transposeMap (a := a)))

theorem conjugateMap_apply (N : Channel a b) (X : CMatrix a) :
    conjugateMap N X = (N.map X.transpose).transpose := rfl

theorem conjugateMap_choi (N : Channel a b) :
    MatrixMap.choi (conjugateMap N) = (MatrixMap.choi N.map).transpose := by
  ext i j
  change N.map (Matrix.single i.1 j.1 1).transpose j.2 i.2 = _
  rw [Matrix.transpose_single]
  rfl

def conjugateChannel (N : Channel a b) : Channel a b where
  map := conjugateMap N
  completelyPositive := by
    change (MatrixMap.choi (conjugateMap N)).PosSemidef
    rw [conjugateMap_choi]
    exact N.completelyPositive.transpose
  tracePreserving X := by
    rw [conjugateMap_apply, Matrix.trace_transpose, N.tracePreserving, Matrix.trace_transpose]
  mapsPositive X hX := by
    rw [conjugateMap_apply]
    exact (N.mapsPositive X.transpose hX.transpose).transpose

theorem partialTranspose_output (N : Channel a b) (X : CMatrix (r × a)) :
    partialTransposeB (amp r N.map X) =
      amp r (conjugateChannel N).map (partialTransposeB X) := by
  ext i j
  change amp r N.map X (i.1, j.2) (j.1, i.2) = _
  rw [amp_apply, amp_apply]
  change N.map (Matrix.of fun k l ↦ X (i.1, k) (j.1, l)) j.2 i.2 =
    (N.map (Matrix.of fun k l ↦ partialTransposeB X (i.1, k) (j.1, l)).transpose).transpose i.2 j.2
  congr 1

theorem isPPT_apply_conditioning (N : Channel a b) (ρ : State (r × a))
    (hρ : QIT.IsPPT ρ) : QIT.IsPPT (((Channel.idChannel r).prod N).applyState ρ) := by
  change (partialTransposeB (amp r N.map ρ.matrix)).PosSemidef
  rw [partialTranspose_output]
  exact ((Channel.idChannel r).prod (conjugateChannel N)).mapsPositive _ hρ

theorem partialTranspose_output_of_channel (N : Channel a b) (hN : IsChannel N)
    (X : CMatrix (r × a)) : partialTransposeB (amp r N.map X) =
      amp r (transposedChannel N hN).map X := by
  ext i j
  change amp r N.map X (i.1, j.2) (j.1, i.2) = _
  rw [amp_apply, amp_apply]
  rfl

theorem output_isPPT (N : Channel a b) (hN : IsChannel N) (ρ : State (r × a)) :
    QIT.IsPPT (((Channel.idChannel r).prod N).applyState ρ) := by
  change (partialTransposeB (amp r N.map ρ.matrix)).PosSemidef
  rw [partialTranspose_output_of_channel N hN]
  exact ((Channel.idChannel r).prod (transposedChannel N hN)).mapsPositive ρ.matrix ρ.pos

theorem prod {N : Channel a b} {M : Channel c d} (hN : IsChannel N) (hM : IsChannel M) :
    IsChannel (N.prod M) := by
  have he : (transposeMap (a := b × d)).comp (N.prod M).map =
      ((transposedChannel N hN).prod (transposedChannel M hM)).map := by
    apply matrixMap_eq_of_kronecker
    intro X Y
    change ((N.prod M).map (X.kronecker Y)).transpose = _
    rw [Channel.prod_map_kronecker, Channel.prod_map_kronecker]
    ext i j
    rfl
  rw [IsChannel, ← transpose_choi, he]
  exact ((transposedChannel N hN).prod (transposedChannel M hM)).completelyPositive

theorem unit : IsChannel (Channel.unit : Channel PUnit.{1} PUnit.{1}) := by
  change (partialTransposeB (MatrixMap.choi (Channel.unit : Channel PUnit.{1} PUnit.{1}).map)).PosSemidef
  have he : partialTransposeB (MatrixMap.choi (Channel.unit : Channel PUnit.{1} PUnit.{1}).map) = 1 := by
    ext i j
    rcases i with ⟨⟨⟩, ⟨⟩⟩
    rcases j with ⟨⟨⟩, ⟨⟩⟩
    rfl
  rw [he]
  exact Matrix.PosSemidef.one

theorem tensorPower {N : Channel a b} (hN : IsChannel N) :
    ∀ n : ℕ, IsChannel (N.tensorPower n)
  | 0 => unit
  | n + 1 => prod hN (tensorPower hN n)

end QuanIncapacity.PPT
