import QuanIncapacity.Activation.FinitePrivateBlock
import QuanIncapacity.Activation.PhysicalSimulation
import QuanIncapacity.Framework.ChannelTensorTransport

/-! Universal activation of every positive-private-capacity channel.
First choose one finite private code, then its finite auxiliary dimension,
then `L = max n d`. The only external premise in the operational terminal
is the quantum coding equality for the actual product channel. -/

noncomputable section
open QIT

namespace QuanIncapacity.Activation

variable {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem positive_padded_code {N : Channel a b} {n k : ℕ} [NeZero k]
    (C : HSWClassicalCode N n (Fin k)) (hC : 0 < codeConversionValue C) :
    ∃ ψ : PureVector (Fin k × QIT.TensorPower (a × Fin 3)
        (max n (Fintype.card (Auxiliary (uniformEnsemble (Fin k) C.encoder))))),
      0 < ((N.prod Λ).tensorPower
        (max n (Fintype.card (Auxiliary (uniformEnsemble (Fin k) C.encoder))))).coherentInformationFor ψ := by
  let c := Auxiliary (uniformEnsemble (Fin k) C.encoder)
  let d := Fintype.card c
  let L := max n d
  have h₁ := (Simulates.refl (N.tensorPower n)).prod (dephasedErasure_simulation c)
  have h₂ := (simulation_tensorPower_pad N n L (le_max_left _ _)).prod
    (simulation_tensorPower_pad Λ d L (le_max_right _ _))
  have h₃ := simulation_tensorPower_pair N Λ L
  exact ((h₁.trans h₂).trans h₃).exists_positive_input
    (globalPurification (uniformEnsemble (Fin k) C.encoder)) hC

/-- Unconditional finite-block information statement. -/
theorem exists_positive_product_block {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (hP : 0 < PrivateCoding.capacity N M) :
    ∃ L : ℕ, 0 < L ∧ ∃ k : ℕ, ∃ (_ : NeZero k),
      ∃ ψ : PureVector (Fin k × QIT.TensorPower (a × Fin 3) L),
        0 < ((N.prod Λ).tensorPower L).coherentInformationFor ψ := by
  obtain ⟨n, hn, k, hk, C, hC⟩ := exists_finite_positive_block hc hP
  obtain ⟨ψ, hψ⟩ := positive_padded_code C hC
  exact ⟨_, hn.trans_le (le_max_left _ _), k, hk, ψ, hψ⟩

/-- `P(N)>0 → Q(N⊗Λ)>0`, with operational private capacity, a certified
full complement, and exactly the product channel's quantum coding theorem. -/
theorem universal_activation {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (hP : 0 < PrivateCoding.capacity N M)
    (coding : External.QuantumCoding (N.prod Λ)) : 0 < (N.prod Λ).quantumCapacity := by
  obtain ⟨L, hL, k, hk, ψ, hψ⟩ := exists_positive_product_block hc hP
  exact quantumCapacity_pos_of_block (N.prod Λ) coding L hL ψ hψ

end QuanIncapacity.Activation
