import QuanIncapacity.Framework.ChannelSimulation
import QuanIncapacity.Framework.ChannelMixture
import QIT.Protocols.LOCC.Core
import QIT.Coding.EntanglementAssisted.Renyi.Petz.Additivity
import QIT.States.Geometry.PureTargetFidelity
import QIT.Coding.Quantum.Basic

/-! Operational finite-round LOCC distillation. Protocols are built from
local CPTP operations, actual finite instruments with conditional channels,
and finite composition; they are not arbitrary channels supplied as LOCC. -/

noncomputable section
open QIT
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.Distillation

inductive Protocol : ∀ (a b c d : Type)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d], Type 1 where
  | local {a b c d : Type}
      [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
      (N : Channel a c) (M : Channel b d) : Protocol a b c d
  | forward {a b c d l : Type}
      [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] [Fintype l]
      (P : OneWayLOCC a c b d l) : Protocol a b c d
  | backward {a b c d l : Type}
      [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] [Fintype l]
      (P : OneWayLOCC b d a c l) : Protocol a b c d
  | comp {a b c d e f : Type}
      [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
      [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
      (P : Protocol a b c d) (Q : Protocol c d e f) : Protocol a b e f

def Protocol.channel {a b c d : Type}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] :
    Protocol a b c d → Channel (a × b) (c × d)
  | @Protocol.local a b c d fa da fb db fc dc fd dd N M =>
      @Channel.prod a c fa da fc dc b d fb db fd dd N M
  | @Protocol.forward _ _ _ _ l _ _ _ _ _ _ _ _ hl P =>
      @OneWayLOCC.realization _ _ _ _ l _ _ _ _ _ _ _ _ hl P
  | @Protocol.backward _ _ _ _ l _ _ _ _ _ _ _ _ hl P =>
      (Channel.reindex (Equiv.prodComm _ _)).comp
        ((@OneWayLOCC.realization _ _ _ _ l _ _ _ _ _ _ _ _ hl P).comp
          (Channel.reindex (Equiv.prodComm _ _)))
  | @Protocol.comp a b c d e f fa da fb db fc dc fd dd fe de ff df P Q =>
      (@Protocol.channel c d e f fc dc fd dd fe de ff df Q).comp
        (@Protocol.channel a b c d fa da fb db fc dc fd dd P)

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

structure Code (ρ : State (a × b)) (n k : ℕ) where
  protocol : Protocol (QIT.TensorPower a n) (QIT.TensorPower b n) (Fin k) (Fin k)

def Code.output {ρ : State (a × b)} {n k : ℕ} (C : Code ρ n k) : State (Fin k × Fin k) :=
  C.protocol.channel.applyState (ρ.tensorPowerBipartite n)

def Code.fidelity {ρ : State (a × b)} {n k : ℕ} [NeZero k] (C : Code ρ n k) : ℝ :=
  (State.maximallyEntangled (Equiv.refl (Fin k))).squaredFidelity C.output

/-- Rate, error and block quantifiers match asymptotically vanishing-error
distillation in ebits per input copy. -/
def Achievable (ρ : State (a × b)) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n → 0 < n → ∃ k : ℕ, ∃ (_ : NeZero k), ∃ C : Code ρ n k,
      R - δ ≤ QIT.log2 (k : ℝ) / n ∧ 1 - ε ≤ C.fidelity

def capacity (ρ : State (a × b)) : ℝ := sSup {R | Achievable ρ R}

structure OneWayCode (ρ : State (a × b)) (n k : ℕ) where
  outcome : Type
  outcome_fintype : Fintype outcome
  protocol : @OneWayLOCC (QIT.TensorPower a n) (Fin k) (QIT.TensorPower b n) (Fin k)
    outcome _ _ _ _ _ _ _ _ outcome_fintype

def OneWayCode.output {ρ : State (a × b)} {n k : ℕ} (C : OneWayCode ρ n k) :
    State (Fin k × Fin k) := by
  letI := C.outcome_fintype
  exact C.protocol.realization.applyState (ρ.tensorPowerBipartite n)

def OneWayCode.fidelity {ρ : State (a × b)} {n k : ℕ} [NeZero k]
    (C : OneWayCode ρ n k) : ℝ :=
  (State.maximallyEntangled (Equiv.refl (Fin k))).squaredFidelity C.output

def OneWayAchievable (ρ : State (a × b)) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n → 0 < n → ∃ k : ℕ, ∃ (_ : NeZero k), ∃ C : OneWayCode ρ n k,
      R - δ ≤ QIT.log2 (k : ℝ) / n ∧ 1 - ε ≤ C.fidelity

def oneWayCapacity (ρ : State (a × b)) : ℝ := sSup {R | OneWayAchievable ρ R}

end QuanIncapacity.Distillation

namespace QuanIncapacity.External

/-- The external Schmidt-rank-two distillation criterion, stated for the
actual finite-round LOCC capacity above. -/
def SchmidtRankTwoDistillation : Prop :=
  ∀ (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b],
    ∀ ρ : State (a × b), ∀ ψ : PureVector (a × b),
      (Matrix.of (fun i j ↦ ψ.amp (i, j))).rank ≤ 2 →
        (star ψ.amp ⬝ᵥ (partialTransposeA ρ.matrix *ᵥ ψ.amp)).re < 0 →
          0 < Distillation.capacity ρ

end QuanIncapacity.External
