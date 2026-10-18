import QuanIncapacity.Activation.HalfErasure
import QuanIncapacity.Activation.UniversalActivation
import QuanIncapacity.Framework.ChannelAssociativity

/-! The final manuscript corollary. The cited four-dimensional private
superactivation result is a named theorem parameter. All regrouping and the
zero private capacity of the second factor are proved internally. -/

noncomputable section
open QIT

namespace QuanIncapacity

namespace External

/-- The precise imported conclusion of Zhu and Wang, Theorem 1, for its
four-input, four-output channel and a certified full complement. -/
def FourDimensionalPrivateSuperactivation {e : Type} [Fintype e] [DecidableEq e]
    (N : Channel (Fin 4) (Fin 4)) (M : Channel (Fin 4) e) : Prop :=
  PrivateCoding.capacity N M = 0 ∧
    0 < PrivateCoding.capacity (N.prod (HalfErasure.channel (a := Fin 2)))
      (M.prod HalfErasure.channel)

/-- Witness-bearing interface for the external existence theorem.
Both channels are actual CPTP objects and their full complementarity is
certified by a common isometry. No global witness or axiom is declared. -/
structure FourDimensionalPrivateSuperactivationWitness where
  environmentDim : ℕ
  channel : Channel (Fin 4) (Fin 4)
  complement : Channel (Fin 4) (Fin environmentDim)
  complementary : ComplementaryChannels channel complement
  result : FourDimensionalPrivateSuperactivation channel complement

end External

namespace NonprivateActivation

def secondFactor : Channel (Fin 2 × Fin 3) (Option (Fin 2) × Fin 3) :=
  HalfErasure.channel.prod Λ

def secondComplement : Channel (Fin 2 × Fin 3) (Option (Fin 2) × Fin 4) :=
  HalfErasure.channel.prod Λc

theorem second_complementary : ComplementaryChannels secondFactor secondComplement :=
  HalfErasure.complementary.prod qutrit_complementary

theorem second_private_zero
    (coding : External.PrivateCoding secondFactor secondComplement) :
    PrivateCoding.capacity secondFactor secondComplement = 0 :=
  qutrit_partner_private_zero HalfErasure.channel HalfErasure.channel
    HalfErasure.complete_order HalfErasure.complementary coding

/-- Both factors have zero operational private capacity and their product
has positive operational quantum capacity. Only the product's quantum coding
theorem and the second factor's private coding theorem are used. -/
theorem two_nonprivate {e : Type} [Fintype e] [DecidableEq e]
    (N : Channel (Fin 4) (Fin 4)) (M : Channel (Fin 4) e)
    (hc : ComplementaryChannels N M)
    (imported : External.FourDimensionalPrivateSuperactivation N M)
    (privateCoding : External.PrivateCoding secondFactor secondComplement)
    (quantumCoding : External.QuantumCoding (N.prod secondFactor)) :
    PrivateCoding.capacity N M = 0 ∧
      PrivateCoding.capacity secondFactor secondComplement = 0 ∧
        0 < (N.prod secondFactor).quantumCapacity := by
  refine ⟨imported.1, second_private_zero privateCoding, ?_⟩
  obtain ⟨L, hL, k, hk, ψ, hψ⟩ := Activation.exists_positive_product_block
    (hc.prod HalfErasure.complementary) imported.2
  have hS := (simulation_prod_assoc N (HalfErasure.channel (a := Fin 2)) Λ).tensorPower L
  obtain ⟨φ, hφ⟩ := hS.exists_positive_input ψ hψ
  exact quantumCapacity_pos_of_block (N.prod secondFactor) quantumCoding L hL φ hφ

theorem dimensions :
    Fintype.card (Fin 4) = 4 ∧ Fintype.card (Fin 4) = 4 ∧
      Fintype.card (Fin 2 × Fin 3) = 6 ∧
        Fintype.card (Option (Fin 2) × Fin 3) = 9 := by
  norm_num

/-- The existential form of the manuscript's last conclusion, using exactly
the chosen external witness and the coding theorems actually needed. -/
theorem exists_two_nonprivate (W : External.FourDimensionalPrivateSuperactivationWitness)
    (privateCoding : External.PrivateCoding secondFactor secondComplement)
    (quantumCoding : External.QuantumCoding (W.channel.prod secondFactor)) :
    ∃ N : Channel (Fin 4) (Fin 4), ∃ M : Channel (Fin 4) (Fin W.environmentDim),
      ComplementaryChannels N M ∧ PrivateCoding.capacity N M = 0 ∧
        PrivateCoding.capacity secondFactor secondComplement = 0 ∧
          0 < (N.prod secondFactor).quantumCapacity :=
  ⟨W.channel, W.complement, W.complementary,
    two_nonprivate W.channel W.complement W.complementary W.result privateCoding quantumCoding⟩

end NonprivateActivation
end QuanIncapacity
