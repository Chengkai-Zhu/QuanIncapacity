import QuanIncapacity.Framework.ForwardAssistance

noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.Distillation

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def localOneWay {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (N : Channel a c) (M : Channel b d) : OneWayLOCC a c b d Unit where
  aliceInstrument :=
    { branch := fun _ ↦ N.map
      branchTraceNonincreasingCP := fun _ ↦ N.traceNonincreasingCP_map
      total := N
      sum_branch_eq_total := by simp }
  bobChannel := fun _ ↦ M
  realization := N.prod M
  realization_map := by simp; rfl

theorem finOneState_unique (ρ σ : State (Fin 1 × Fin 1)) : ρ = σ := by
  apply State.ext
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i; fin_cases j; fin_cases k; fin_cases l
  have hρ := ρ.trace_eq_one
  have hσ := σ.trace_eq_one
  norm_num [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_succ] at hρ hσ
  exact hρ.trans hσ.symm

def oneWayZeroCode (ρ : State (a × b)) (n : ℕ) : OneWayCode ρ n 1 where
  outcome := Unit
  outcome_fintype := inferInstance
  protocol := localOneWay (Channel.replacer (basisState (0 : Fin 1)))
    (Channel.replacer (basisState (0 : Fin 1)))

theorem oneWayZeroCode_fidelity (ρ : State (a × b)) (n : ℕ) :
    (oneWayZeroCode ρ n).fidelity = 1 := by
  unfold OneWayCode.fidelity
  rw [finOneState_unique (oneWayZeroCode ρ n).output
      (State.maximallyEntangled (Equiv.refl (Fin 1))),
    State.squaredFidelity_self_eq_traceNorm_matrix_sq,
    traceNorm_posSemidef_eq_trace_re _ (State.maximallyEntangled (Equiv.refl (Fin 1))).pos,
    (State.maximallyEntangled (Equiv.refl (Fin 1))).trace_re_eq_one]
  norm_num

theorem oneWay_rate_zero (ρ : State (a × b)) : OneWayAchievable ρ 0 := by
  intro δ hδ ε hε
  refine ⟨0, fun n _ _ ↦ ⟨1, inferInstance, oneWayZeroCode ρ n, ?_, ?_⟩⟩
  · simp [QIT.log2]
    exact hδ.le
  · rw [oneWayZeroCode_fidelity]
    linarith

theorem oneWayCapacity_eq_zero [Nonempty a] (N : Channel a b)
    (forward : External.ForwardClassicalNoIncreaseQuantumCapacity N)
    (hQ : N.quantumCapacity = 0) : oneWayCapacity (ForwardAssistance.choiState N) = 0 := by
  have hbound (R : ℝ) (hR : OneWayAchievable (ForwardAssistance.choiState N) R) : R ≤ 0 := by
    have h := forward R (ForwardAssistance.oneWay_achievable_forward hR)
    rwa [hQ] at h
  have hz := oneWay_rate_zero (ForwardAssistance.choiState N)
  exact le_antisymm (csSup_le ⟨0, hz⟩ hbound) (le_csSup ⟨0, hbound⟩ hz)

end QuanIncapacity.Distillation
