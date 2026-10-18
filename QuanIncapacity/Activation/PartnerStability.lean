import QuanIncapacity.Qutrit.ZeroCapacity

/-! Stability under a completely dominated partner, including every
antidegradable partner. Each capacity conclusion takes only its own coding
contract for the product channel. -/

noncomputable section
open QIT

namespace QuanIncapacity

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem completeRelativeEntropyOrder_of_degrading (M : Channel a e) (D : Channel e b) :
    CompleteRelativeEntropyOrder (D.comp M) M := by
  intro r _ _ _ ρ σ _
  rw [← amp_applyState_comp, ← amp_applyState_comp]
  exact State.relativeEntropy_dataProcessing_channel_ge
    (((Channel.idChannel r).prod M).applyState ρ)
    (((Channel.idChannel r).prod M).applyState σ) ((Channel.idChannel r).prod D)

theorem completeRelativeEntropyOrder_of_antidegradable {N : Channel a b} {M : Channel a e}
    (h : ∃ D : Channel e b, D.map.comp M.map = N.map) : CompleteRelativeEntropyOrder N M := by
  obtain ⟨D, hD⟩ := h
  have hN : D.comp M = N := channel_eq_of_map_eq _ _ hD
  rw [← hN]
  exact completeRelativeEntropyOrder_of_degrading M D

theorem qutrit_partner_private_zero [Nonempty a] [Nonempty b] [Nonempty e]
    (N : Channel a b) (M : Channel a e) (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) (coding : External.PrivateCoding (N.prod Λ) (M.prod Λc)) :
    PrivateCoding.capacity (N.prod Λ) (M.prod Λc) = 0 :=
  (h.prod qutrit_complete_relativeEntropy_order).privateCapacity_eq_zero
    (hc.prod qutrit_complementary) coding

theorem qutrit_partner_quantum_zero [Nonempty a] [Nonempty b] [Nonempty e]
    (N : Channel a b) (M : Channel a e) (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) (coding : External.QuantumCoding (N.prod Λ)) :
    (N.prod Λ).quantumCapacity = 0 :=
  (h.prod qutrit_complete_relativeEntropy_order).quantumCapacity_eq_zero
    (hc.prod qutrit_complementary) coding

end QuanIncapacity
