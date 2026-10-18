import QuanIncapacity.Framework.PPTFidelity
import QIT.States.MaximallyMixed

/-! The operational PPT quantum-capacity converse, proved from actual
encoding/decoding codes and squared-fidelity bounds, without a coding theorem. -/

noncomputable section
open QIT

namespace QuanIncapacity

variable {a b r t : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype r] [DecidableEq r] [Nonempty r]
variable [Fintype t] [DecidableEq t]

theorem PPT.generationCode_fidelity {N : Channel a b} (hN : PPT.IsChannel N)
    (C : EntanglementGenerationCode N r t) : C.fidelity ≤ (Fintype.card r : ℝ)⁻¹ := by
  exact PPT.fidelity_le_inv_card C.outputState
    (PPT.isPPT_apply_conditioning C.decoder C.channelOutput
      (PPT.output_isPPT N hN C.encodedState)) C.pairing

theorem unit_state_unique (ρ σ : State (PUnit.{1} × PUnit.{1})) : ρ = σ := by
  apply State.ext
  ext ⟨⟨⟩, ⟨⟩⟩ ⟨⟨⟩, ⟨⟩⟩
  simpa only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fintype.sum_unique] using
    ρ.trace_eq_one.trans σ.trace_eq_one.symm

theorem quantum_rate_zero [Nonempty a] (N : Channel a b) : N.IsAchievableQuantumRate 0 := by
  intro δ hδ ε hε
  refine ⟨0, fun n _ _ ↦ ?_⟩
  have : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty _
  let C : EntanglementTransmissionCode (N.tensorPower n) PUnit.{1} PUnit.{1} PUnit.{1} :=
    { encoder := Channel.replacer (State.maximallyMixed (QIT.TensorPower a n))
      decoder := Channel.traceToUnit (QIT.TensorPower b n)
      inputPairing := Equiv.refl _
      targetPairing := Equiv.refl _ }
  have hf : C.fidelity = 1 := by
    change (EntanglementGenerationCode.ofTransmission C).outputState.squaredFidelity
      (EntanglementGenerationCode.ofTransmission C).targetState = 1
    rw [unit_state_unique (EntanglementGenerationCode.ofTransmission C).outputState
        (EntanglementGenerationCode.ofTransmission C).targetState,
      State.squaredFidelity_self_eq_traceNorm_matrix_sq,
      traceNorm_posSemidef_eq_trace_re _ (EntanglementGenerationCode.ofTransmission C).targetState.pos,
      (EntanglementGenerationCode.ofTransmission C).targetState.trace_re_eq_one]
    norm_num
  refine ⟨PUnit.{1}, inferInstance, inferInstance, inferInstance, C, ?_, ?_⟩
  · simp [EntanglementTransmissionCode.rate, EntanglementGenerationCode.rate,
      EntanglementGenerationCode.logDimension, EntanglementGenerationCode.dimension, log2]
    exact hδ.le
  · change 1 - C.fidelity ≤ ε
    rw [hf]
    simpa using hε.le

namespace PPT

theorem achievable_nonpos {N : Channel a b} (hN : IsChannel N) {R : ℝ}
    (hR : N.IsAchievableQuantumRate R) : R ≤ 0 := by
  by_contra h
  have hpos : 0 < R := lt_of_not_ge h
  obtain ⟨n₀, hn₀⟩ := hR (R / 2) (by positivity) (1 / 4) (by norm_num)
  let n := n₀ + 1
  have hn : 0 < n := by omega
  obtain ⟨M, iF, iD, iN, C, hrate, herr⟩ := hn₀ n (by omega) hn
  have hK : 2 ≤ Fintype.card M := by
    by_contra hk
    have hcard : Fintype.card M = 1 := by
      have hc : 0 < Fintype.card M := Fintype.card_pos
      omega
    have hz : C.rate n = 0 := by
      simp [EntanglementTransmissionCode.rate, EntanglementGenerationCode.rate,
        EntanglementGenerationCode.logDimension, EntanglementGenerationCode.dimension,
        EntanglementGenerationCode.ofTransmission, hcard, log2]
    rw [hz] at hrate
    linarith
  have hfid := generationCode_fidelity (tensorPower hN n)
    (EntanglementGenerationCode.ofTransmission C)
  have hlow := (EntanglementGenerationCode.error_le_iff
    (EntanglementGenerationCode.ofTransmission C) (1 / 4)).mp herr
  have hi : (Fintype.card M : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) (by exact_mod_cast hK)
  norm_num at hi hlow
  linarith

theorem quantumCapacity_eq_zero [Nonempty a] {N : Channel a b} (hN : IsChannel N) :
    N.quantumCapacity = 0 := by
  have hz : 0 ∈ {R : ℝ | N.IsAchievableQuantumRate R} := quantum_rate_zero N
  have hb : BddAbove {R : ℝ | N.IsAchievableQuantumRate R} :=
    ⟨0, fun R hR ↦ achievable_nonpos hN hR⟩
  apply le_antisymm
  · exact csSup_le ⟨0, hz⟩ (fun R hR ↦ achievable_nonpos hN hR)
  · exact le_csSup hb hz

end PPT
end QuanIncapacity
