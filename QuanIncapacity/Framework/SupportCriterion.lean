import QuanIncapacity.Framework.SupportAmplification
import QuanIncapacity.Framework.AllBlockInformation

/-! The general shadowing criterion without any assumption that the original
identity outputs have full rank. Support compression is proved internally. -/

noncomputable section
open QIT QuanIncapacity.MatrixSpace
open scoped Matrix ComplexOrder MatrixOrder

namespace QuanIncapacity.OutputSupport

variable {a b e r : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
variable [Fintype r] [DecidableEq r]

def shadowMap (N : Channel a b) (M : Channel a e) (J : MatrixMap b e) :
    MatrixMap (Space N) (Space M) :=
  (IsometryCompression.map (inclusion M)).comp
    (J.comp (MatrixMap.ofReferenceIsometry (inclusion N)))

theorem shadowMap_amp (N : Channel a b) (M : Channel a e) (J : MatrixMap b e)
    (Y : CMatrix (r × Space N)) :
    amp r (shadowMap N M J) Y =
      IsometryCompression.map (IsometryCompression.lift r (inclusion M))
        (amp r J ((IsometryCompression.lift r (inclusion N)).matrix * Y *
          (IsometryCompression.lift r (inclusion N)).matrix.conjTranspose)) := by
  rw [shadowMap, amp_comp, amp_comp]
  change amp r (IsometryCompression.map (inclusion M))
    (amp r J (amp r (MatrixMap.ofReferenceIsometry (inclusion N)) Y)) = _
  rw [IsometryCompression.amp_compression, IsometryCompression.amp_embedding]

theorem unbiased_shadow {N : Channel a b} {M : Channel a e} {J : MatrixMap b e}
    (h : Shadowing.IsUnbiasedShadow N.map M.map J) :
    Shadowing.IsUnbiasedShadow (channel N).map (channel M).map (shadowMap N M J) := by
  refine ⟨?_, ?_⟩
  · intro Y
    change IsometryCompression.map (inclusion M)
      (J (MatrixMap.ofReferenceIsometry (inclusion N) Y.conjTranspose)) =
      (IsometryCompression.map (inclusion M)
        (J (MatrixMap.ofReferenceIsometry (inclusion N) Y))).conjTranspose
    have he := channel_map_adjoint (Channel.ofReferenceIsometry (inclusion N)) Y
    change MatrixMap.ofReferenceIsometry (inclusion N) Y.conjTranspose =
      (MatrixMap.ofReferenceIsometry (inclusion N) Y).conjTranspose at he
    calc
      _ = IsometryCompression.map (inclusion M)
        (J (MatrixMap.ofReferenceIsometry (inclusion N) Y).conjTranspose) :=
          congrArg (fun Z ↦ IsometryCompression.map (inclusion M) (J Z)) he
      _ = _ := by rw [h.map_adjoint, IsometryCompression.map_adjoint]
  · intro X Y
    have hn := IsometryCompression.trace_pairing (inclusion N) ((channel N).map X)
      ((inclusion N).matrix * Y * (inclusion N).matrix.conjTranspose)
    rw [reconstruct, IsometryCompression.map_image] at hn
    have hm := IsometryCompression.trace_pairing (inclusion M) ((channel M).map X)
      (J ((inclusion N).matrix * Y * (inclusion N).matrix.conjTranspose))
    rw [reconstruct] at hm
    change ((channel N).map X * Y).trace =
      ((channel M).map X * IsometryCompression.map (inclusion M)
        (J (MatrixMap.ofReferenceIsometry (inclusion N) Y))).trace
    rw [MatrixMap.ofReferenceIsometry_apply]
    exact hn.symm.trans ((h.mean_eq X _).trans hm)

theorem complete_shadow {N : Channel a b} {M : Channel a e} {J : MatrixMap b e}
    (h : Shadowing.IsCompleteShadow N.map M.map J) :
    Shadowing.IsCompleteShadow (channel N).map (channel M).map (shadowMap N M J) := by
  refine ⟨unbiased_shadow h.1, ?_⟩
  intro r _ _ ρ Y hY
  let U := IsometryCompression.lift r (inclusion N)
  let V := IsometryCompression.lift r (inclusion M)
  let Yhat := U.matrix * Y * U.matrix.conjTranspose
  let T := amp r J Yhat
  have hYhat : Yhat.IsHermitian := by
    simp only [Yhat, Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hY.eq, Matrix.mul_assoc]
  have hT : T.IsHermitian := by
    change (amp r J Yhat).conjTranspose = amp r J Yhat
    rw [← amp_map_adjoint J h.1.map_adjoint, hYhat.eq]
  have hMρ : (amp r (channel M).map ρ.matrix).PosSemidef :=
    ((Channel.idChannel r).prod (channel M)).mapsPositive ρ.matrix ρ.pos
  have hcmp := IsometryCompression.variance_le V hMρ hT
  have hv := h.2 r ρ Yhat hYhat
  rw [amplified_matrix M, amplified_matrix N] at hv
  have heq := IsometryCompression.variance_image U (amp r (channel N).map ρ.matrix) Y
  rw [shadowMap_amp]
  exact hcmp.trans (hv.trans_eq heq)

end QuanIncapacity.OutputSupport

namespace QuanIncapacity.Shadowing

variable {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

/-- Full generality of the manuscript's output-support reduction lemma and
relative-entropy criterion. No faithful identity-output premise remains. -/
theorem complete_relativeEntropy_order_of_shadow
    (N : Channel a b) (M : Channel a e) (J : MatrixMap b e)
    (h : IsCompleteShadow N.map M.map J) : CompleteRelativeEntropyOrder N M := by
  have : Nonempty (OutputSupport.Space N) := OutputSupport.nonempty N
  have : Nonempty (OutputSupport.Space M) := OutputSupport.nonempty M
  have h₀ := complete_relativeEntropy_order (OutputSupport.channel N) (OutputSupport.channel M)
    (OutputSupport.shadowMap N M J) (OutputSupport.complete_shadow h)
    (OutputSupport.identity_posDef N) (OutputSupport.identity_posDef M)
  intro r _ _ _ ρ σ hs
  have hn := relativeEntropy_isometry (IsometryCompression.lift r (OutputSupport.inclusion N))
    (((Channel.idChannel r).prod (OutputSupport.channel N)).applyState ρ)
    (((Channel.idChannel r).prod (OutputSupport.channel N)).applyState σ)
    (State.channel_map_supports _ σ.pos hs)
  have hm := relativeEntropy_isometry (IsometryCompression.lift r (OutputSupport.inclusion M))
    (((Channel.idChannel r).prod (OutputSupport.channel M)).applyState ρ)
    (((Channel.idChannel r).prod (OutputSupport.channel M)).applyState σ)
    (State.channel_map_supports _ σ.pos hs)
  rw [← OutputSupport.amplified_output, ← OutputSupport.amplified_output] at hn hm
  rw [hn, hm]
  exact h₀ r ρ σ hs

theorem privateCapacity_eq_zero [Nonempty b] [Nonempty e]
    {N : Channel a b} {M : Channel a e} {J : MatrixMap b e}
    (h : IsCompleteShadow N.map M.map J) (hc : ComplementaryChannels N M)
    (coding : External.PrivateCoding N M) : PrivateCoding.capacity N M = 0 :=
  (complete_relativeEntropy_order_of_shadow N M J h).privateCapacity_eq_zero hc coding

theorem quantumCapacity_eq_zero [Nonempty b] [Nonempty e]
    {N : Channel a b} {M : Channel a e} {J : MatrixMap b e}
    (h : IsCompleteShadow N.map M.map J) (hc : ComplementaryChannels N M)
    (coding : External.QuantumCoding N) : N.quantumCapacity = 0 :=
  (complete_relativeEntropy_order_of_shadow N M J h).quantumCapacity_eq_zero hc coding

end QuanIncapacity.Shadowing
