import QuanIncapacity.Framework.Distillation

/-! Forward classical assistance with arbitrary mixed sender-prepared input
and actual one-way LOCC processing of the reference and receiver output. -/

noncomputable section
open QIT

namespace QuanIncapacity.ForwardAssistance

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

structure Code (N : Channel a b) (n k : ℕ) where
  reference : Type
  reference_fintype : Fintype reference
  reference_decidableEq : DecidableEq reference
  encodedState : letI := reference_fintype; letI := reference_decidableEq
    State (reference × QIT.TensorPower a n)
  outcome : Type
  outcome_fintype : Fintype outcome
  protocol : letI := reference_fintype; letI := reference_decidableEq
    letI := outcome_fintype
    OneWayLOCC reference (Fin k) (QIT.TensorPower b n) (Fin k) outcome

def Code.output {N : Channel a b} {n k : ℕ} (C : Code N n k) : State (Fin k × Fin k) := by
  letI := C.reference_fintype
  letI := C.reference_decidableEq
  letI := C.outcome_fintype
  exact C.protocol.realization.applyState
    (((Channel.idChannel C.reference).prod (N.tensorPower n)).applyState C.encodedState)

def Code.fidelity {N : Channel a b} {n k : ℕ} [NeZero k] (C : Code N n k) : ℝ :=
  (State.maximallyEntangled (Equiv.refl (Fin k))).squaredFidelity C.output

def Achievable (N : Channel a b) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n → 0 < n → ∃ k : ℕ, ∃ (_ : NeZero k), ∃ C : Code N n k,
      R - δ ≤ QIT.log2 (k : ℝ) / n ∧ 1 - ε ≤ C.fidelity

variable [Nonempty a]

def choiState (N : Channel a b) : State (a × b) :=
  N.hypothesisTestingOutputState (PureVector.maximallyEntangled (Equiv.refl a))

def fromOneWayCode {N : Channel a b} {n k : ℕ}
    (C : Distillation.OneWayCode (choiState N) n k) : Code N n k where
  reference := QIT.TensorPower a n
  reference_fintype := inferInstance
  reference_decidableEq := inferInstance
  encodedState := ((PureVector.maximallyEntangled (Equiv.refl a)).tensorPowerBipartite n).state
  outcome := C.outcome
  outcome_fintype := C.outcome_fintype
  protocol := C.protocol

theorem fromOneWayCode_output {N : Channel a b} {n k : ℕ}
    (C : Distillation.OneWayCode (choiState N) n k) :
    (fromOneWayCode C).output = C.output := by
  letI := C.outcome_fintype
  change C.protocol.realization.applyState
    ((N.tensorPower n).hypothesisTestingOutputState
      ((PureVector.maximallyEntangled (Equiv.refl a)).tensorPowerBipartite n)) = _
  rw [Channel.hypothesisTestingOutputState_tensorPowerBipartite]
  rfl

theorem fromOneWayCode_fidelity {N : Channel a b} {n k : ℕ} [NeZero k]
    (C : Distillation.OneWayCode (choiState N) n k) :
    (fromOneWayCode C).fidelity = C.fidelity := by
  unfold Code.fidelity Distillation.OneWayCode.fidelity
  rw [fromOneWayCode_output]

theorem oneWay_achievable_forward {N : Channel a b} {R : ℝ}
    (h : Distillation.OneWayAchievable (choiState N) R) : Achievable N R := by
  intro δ hδ ε hε
  obtain ⟨n₀, hn₀⟩ := h δ hδ ε hε
  refine ⟨n₀, fun n hn hpos ↦ ?_⟩
  obtain ⟨k, hk, C, hrate, hf⟩ := hn₀ n hn hpos
  refine ⟨k, hk, fromOneWayCode C, hrate, ?_⟩
  rwa [fromOneWayCode_fidelity]

end QuanIncapacity.ForwardAssistance

namespace QuanIncapacity.External

/-- The external forward-classical-assistance theorem. Every achievable
rate of these actual assisted entanglement-generation codes is bounded by
the unassisted Lean-QIT operational quantum capacity. -/
def ForwardClassicalNoIncreaseQuantumCapacity {a b : Type}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (N : Channel a b) : Prop :=
  ∀ R : ℝ, ForwardAssistance.Achievable N R → R ≤ N.quantumCapacity

end QuanIncapacity.External
