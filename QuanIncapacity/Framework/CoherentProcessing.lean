import QuanIncapacity.Framework.ComplementaryInformation

/-! Coherent information under physical decoding and isometric encoding.
The optimization uses the input-sized reference from Lean-QIT; arbitrary
finite reference registers are reduced to it through a common Stinespring
dilation, rather than silently changing the optimization domain. -/

noncomputable section
open QIT
open scoped Matrix

namespace QuanIncapacity

variable {a b c r : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
variable [Fintype r] [DecidableEq r]

theorem exists_complementaryChannel (N : Channel a b) :
    ∃ M : Channel a (a × b), ComplementaryChannels N M := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd N.map N.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact N.tracePreserving
  let V := MatrixMap.krausStinespringIsometry K hTP
  refine ⟨V.complementaryChannel, V, ?_, rfl⟩
  apply V.outputChannel_eq_of_realizes
  intro X
  rw [MatrixMap.partialTraceB_krausStinespringIsometry, ← hK]

theorem coherentInformationFor_le_optimized (N : Channel a b)
    (ψ : PureVector (r × a)) : N.coherentInformationFor ψ ≤ N.coherentInformation := by
  obtain ⟨M, hc⟩ := exists_complementaryChannel N
  rw [hc.coherentInformationFor_eq]
  have h := N.coherentInformationFor_le ψ.state.marginalB.canonicalPurification
  rw [hc.coherentInformationFor_eq] at h
  simpa only [show ψ.state.marginalB.canonicalPurification.state.marginalB =
    ψ.state.marginalB from State.ext ψ.state.marginalB.canonicalPurification_purifies] using h

theorem coherentInformation_decode_le (ρ : State (r × b)) (D : Channel b c) :
    (((Channel.idChannel r).prod D).applyState ρ).coherentInformation ≤
      ρ.coherentInformation := by
  have h := QIT.mutualInformation_dataProcessing_local_channels_ge ρ
    (Channel.idChannel r) D
  simp only [mutualInformation, State.marginalA_applyState_prod,
    State.idChannel_applyState] at h
  simp only [State.coherentInformation_eq]
  linarith

theorem coherentInformationFor_decode_le (N : Channel a b) (D : Channel b c)
    (ψ : PureVector (r × a)) :
    (D.comp N).coherentInformationFor ψ ≤ N.coherentInformationFor ψ := by
  unfold Channel.coherentInformationFor
  rw [← amp_applyState_comp]
  exact coherentInformation_decode_le _ D

theorem isometry_pureState_right (V : ReferenceIsometry a b) (ψ : PureVector (r × a)) :
    (V.applyPureVectorRight ψ).state =
      ((Channel.idChannel r).prod (Channel.ofReferenceIsometry V)).applyState ψ.state := by
  apply State.ext
  rw [V.rankOne_applyPureVectorRight]
  exact (MatrixMap.kron_id_ofReferenceIsometry_apply_eq_applyMatrixRight V ψ.state.matrix).symm

theorem coherentInformationFor_encode (N : Channel b c) (V : ReferenceIsometry a b)
    (ψ : PureVector (r × a)) :
    (N.comp (Channel.ofReferenceIsometry V)).coherentInformationFor ψ =
      N.coherentInformationFor (V.applyPureVectorRight ψ) := by
  simp only [Channel.coherentInformationFor, isometry_pureState_right,
    amp_applyState_comp]

/-- Every positive finite block, with any finite reference, yields a positive
operational quantum capacity under the external quantum coding
equality for this channel. -/
theorem quantumCapacity_pos_of_block [Nonempty a] (N : Channel a b)
    (hcode : External.QuantumCoding N) (n : ℕ) (hn : 0 < n)
    (ψ : PureVector (r × QIT.TensorPower a n))
    (hψ : 0 < (N.tensorPower n).coherentInformationFor ψ) : 0 < N.quantumCapacity := by
  rw [hcode]
  exact (div_pos (hψ.trans_le (coherentInformationFor_le_optimized _ ψ))
    (by exact_mod_cast hn)).trans_le (N.blockCoherentInformationRate_le_regularized n hn)

end QuanIncapacity
