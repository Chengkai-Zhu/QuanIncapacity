import QuanIncapacity.Framework.InformationOrder
import QuanIncapacity.Framework.TensorOrder
import QIT.Information.AlickiFannesWinter

/-! Entropic identities for channels certified by one Stinespring isometry. -/

noncomputable section
open QIT
open scoped ComplexOrder MatrixOrder BigOperators

namespace QuanIncapacity

variable {a b e r : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
variable [Fintype r] [DecidableEq r]

namespace Stinespring

theorem pureOutput_marginalB (V : ReferenceIsometry a (b × e)) (ψ : PureVector (r × a)) :
    (V.applyPureVectorRight ψ).state.marginalB =
      (Channel.ofReferenceIsometry V).applyState ψ.state.marginalB := by
  apply State.ext
  rw [State.marginalB_matrix, V.rankOne_applyPureVectorRight,
    V.partialTraceA_applyMatrixRight]
  exact (MatrixMap.ofReferenceIsometry_apply V ψ.state.marginalB.matrix).symm

theorem pureOutput_receiver (V : ReferenceIsometry a (b × e)) (ψ : PureVector (r × a)) :
    ((V.applyPureVectorRight ψ).reindex (Equiv.prodAssoc r b e).symm).state.marginalA =
      ((Channel.idChannel r).prod V.outputChannel).applyState ψ.state := by
  apply State.ext
  ext i j
  simp only [PureVector.reindex_state, State.marginalA_matrix, State.reindex_matrix,
    V.rankOne_applyPureVectorRight]
  change (∑ k : e, V.applyMatrixRight ψ.state.matrix (i.1, (i.2, k)) (j.1, (j.2, k))) =
    MatrixMap.kron (Channel.idChannel r).map V.outputChannel.map ψ.state.matrix i j
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  exact (congrFun (congrFun (V.outputChannel_map
    (fun k l ↦ ψ.state.matrix (i.1, k) (j.1, l))) i.2) j.2).symm

theorem pureOutput_environment (V : ReferenceIsometry a (b × e)) (ψ : PureVector (r × a)) :
    ((V.applyPureVectorRight ψ).reindex (referenceLast r b e)).state.marginalA =
      ((Channel.idChannel r).prod V.complementaryChannel).applyState ψ.state := by
  apply State.ext
  ext i j
  simp only [PureVector.reindex_state, State.marginalA_matrix, State.reindex_matrix,
    V.rankOne_applyPureVectorRight]
  change (∑ k : b, V.applyMatrixRight ψ.state.matrix (i.1, (k, i.2)) (j.1, (k, j.2))) =
    MatrixMap.kron (Channel.idChannel r).map V.complementaryChannel.map ψ.state.matrix i j
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  exact (congrFun (congrFun (V.complementaryChannel_map
    (fun k l ↦ ψ.state.matrix (i.1, k) (j.1, l))) i.2) j.2).symm

theorem receiver_reference_entropy (V : ReferenceIsometry a (b × e))
    (ψ : PureVector (r × a)) :
    (((Channel.idChannel r).prod V.outputChannel).applyState ψ.state).vonNeumann =
      (V.complementaryChannel.applyState ψ.state.marginalB).vonNeumann := by
  have hd := State.pureVector_marginalA_vonNeumann_eq_marginalB
    ((V.applyPureVectorRight ψ).reindex (Equiv.prodAssoc r b e).symm)
  rw [pureOutput_receiver] at hd
  have hm : ((V.applyPureVectorRight ψ).reindex (Equiv.prodAssoc r b e).symm).state.marginalB =
      (V.applyPureVectorRight ψ).state.marginalB.marginalB := by
    apply State.ext
    ext i j
    simp only [PureVector.reindex_state, State.reindex_matrix, State.marginalB_matrix,
      partialTraceA, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.prodAssoc_apply,
      Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hm, pureOutput_marginalB, ← V.complementaryChannel_applyState] at hd
  exact hd

theorem environment_reference_entropy (V : ReferenceIsometry a (b × e))
    (ψ : PureVector (r × a)) :
    (((Channel.idChannel r).prod V.complementaryChannel).applyState ψ.state).vonNeumann =
      (V.outputChannel.applyState ψ.state.marginalB).vonNeumann := by
  have hd := State.pureVector_marginalA_vonNeumann_eq_marginalB
    ((V.applyPureVectorRight ψ).reindex (referenceLast r b e))
  rw [pureOutput_environment] at hd
  have hm : ((V.applyPureVectorRight ψ).reindex (referenceLast r b e)).state.marginalB =
      (V.applyPureVectorRight ψ).state.marginalB.marginalA := by
    apply State.ext
    ext i j
    simp only [PureVector.reindex_state, State.reindex_matrix, State.marginalB_matrix,
      State.marginalA_matrix, partialTraceA, partialTraceB, referenceLast,
      Matrix.submatrix_apply, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hm, pureOutput_marginalB, ← V.outputChannel_applyState] at hd
  exact hd

end Stinespring

theorem ComplementaryChannels.coherentInformationFor_eq
    {N : Channel a b} {M : Channel a e} (hc : ComplementaryChannels N M)
    (ψ : PureVector (r × a)) :
    N.coherentInformationFor ψ = Information.coherent N M ψ.state.marginalB := by
  obtain ⟨V, rfl, rfl⟩ := hc
  rw [Channel.coherentInformationFor, State.coherentInformation_eq,
    State.marginalB_applyState_prod, Stinespring.receiver_reference_entropy]
  rfl

theorem ComplementaryChannels.mutualInformation_sub_eq
    {N : Channel a b} {M : Channel a e} (hc : ComplementaryChannels N M)
    (ψ : PureVector (r × a)) :
    mutualInformation (((Channel.idChannel r).prod N).applyState ψ.state) -
        mutualInformation (((Channel.idChannel r).prod M).applyState ψ.state) =
      2 * Information.coherent N M ψ.state.marginalB := by
  obtain ⟨V, rfl, rfl⟩ := hc
  simp only [mutualInformation, State.marginalA_applyState_prod,
    State.marginalB_applyState_prod, State.idChannel_applyState,
    Stinespring.receiver_reference_entropy, Stinespring.environment_reference_entropy,
    Information.coherent]
  ring

theorem CompleteRelativeEntropyOrder.coherent_nonpos [Nonempty a]
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) (ρ : State a) : Information.coherent N M ρ ≤ 0 := by
  have hh := h.mutualInformation_le ρ.canonicalPurification.state
  have he := hc.mutualInformation_sub_eq ρ.canonicalPurification
  rw [show ρ.canonicalPurification.state.marginalB = ρ from
    State.ext ρ.canonicalPurification_purifies] at he
  linarith

theorem zero_mem_coherentInformationValues [Nonempty a] (N : Channel a b) :
    0 ∈ N.coherentInformationValues := by
  let ψ : PureVector a :=
    { amp := Pi.single (Classical.arbitrary a) 1
      trace_rankOne_eq_one := by simp [rankOneMatrix_trace, dotProduct, Pi.single_apply] }
  refine ⟨ψ.prod ψ, ?_⟩
  simp [Channel.coherentInformationFor, State.coherentInformation_eq, PureVector.prod_state,
    Channel.applyState_prod, State.idChannel_applyState, State.vonNeumann_prod,
    State.pureVector_vonNeumann_eq_zero, State.marginalB, State.partialTraceA_prod]

theorem CompleteRelativeEntropyOrder.coherentInformation_eq_zero [Nonempty a]
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) : N.coherentInformation = 0 := by
  have hz := zero_mem_coherentInformationValues N
  apply le_antisymm
  · apply csSup_le ⟨0, hz⟩
    rintro x ⟨ψ, rfl⟩
    change N.coherentInformationFor ψ ≤ 0
    rw [hc.coherentInformationFor_eq]
    exact h.coherent_nonpos hc _
  · exact le_csSup N.coherentInformationValues_bddAbove hz

end QuanIncapacity
