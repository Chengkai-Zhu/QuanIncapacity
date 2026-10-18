import QuanIncapacity.Framework.ChannelPair

/-! Finite CPTP mixtures and deterministic basis preparations. -/

noncomputable section
open QIT
open scoped ComplexOrder MatrixOrder BigOperators

namespace QuanIncapacity

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def channelMix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N M : Channel a b) : Channel a b where
  map := p • N.map + (1 - p) • M.map
  completelyPositive := by
    have he : MatrixMap.choi (p • N.map + (1 - p) • M.map) =
        p • MatrixMap.choi N.map + (1 - p) • MatrixMap.choi M.map := by ext i j; rfl
    change (MatrixMap.choi _).PosSemidef
    rw [he]
    exact (N.completelyPositive.smul hp0).add (M.completelyPositive.smul (sub_nonneg.mpr hp1))
  tracePreserving := by
    intro X
    change (p • N.map X + (1 - p) • M.map X).trace = X.trace
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      N.tracePreserving, M.tracePreserving]
    simp only [← add_smul, add_sub_cancel, one_smul]
  mapsPositive := fun X hX ↦
    ((N.mapsPositive X hX).smul hp0).add ((M.mapsPositive X hX).smul (sub_nonneg.mpr hp1))

theorem channelMix_map (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N M : Channel a b) (X : CMatrix a) :
    (channelMix p hp0 hp1 N M).map X = p • N.map X + (1 - p) • M.map X := rfl

def basisState (i : a) : State a :=
  (PureVector.mk (Pi.single i 1) (by simp [rankOneMatrix_trace, dotProduct, Pi.single_apply])).state

theorem basisState_matrix (i : a) : (basisState i).matrix = Matrix.single i i 1 := by
  ext j k
  by_cases hj : j = i <;> by_cases hk : k = i <;>
    simp [basisState, PureVector.state_matrix_apply, Matrix.single_apply, hj, hk, eq_comm,
      PureVector.state, rankOneMatrix_apply, Pi.single_apply] <;> aesop

end QuanIncapacity
