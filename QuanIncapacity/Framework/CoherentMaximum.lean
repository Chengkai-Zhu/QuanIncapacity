import QuanIncapacity.Framework.InformationSuperadditivity
import QIT.Channels.Topology

/-! The manuscript's attained maximum, connected to Lean-QIT's supremum
optimization over input-sized purifications. -/
noncomputable section
open QIT

namespace QuanIncapacity
variable {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem coherentInformationFor_continuous (N : Channel a b) :
    Continuous (fun ψ : PureVector (a × a) ↦ N.coherentInformationFor ψ) :=
  State.conditionalEntropy_continuous.neg.comp
    ((((Channel.idChannel a).prod N).applyState_continuous).comp PureVector.state_continuous)

theorem exists_coherentInformation_maximizer (N : Channel a b) :
    ∃ ψ : PureVector (a × a), N.coherentInformation = N.coherentInformationFor ψ := by
  haveI : Nonempty (PureVector (a × a)) := ⟨PureVector.maximallyEntangled (Equiv.refl a)⟩
  obtain ⟨ψ, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (coherentInformationFor_continuous N).continuousOn
  refine ⟨ψ, le_antisymm ?_ (N.coherentInformationFor_le ψ)⟩
  apply csSup_le N.coherentInformationValues_nonempty
  rintro x ⟨φ, rfl⟩
  exact hmax trivial

theorem ComplementaryChannels.coherent_maximum {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) :
    ∃ ρ : State a, Information.coherent N M ρ = N.coherentInformation ∧
      ∀ σ : State a, Information.coherent N M σ ≤ Information.coherent N M ρ := by
  obtain ⟨ψ, hψ⟩ := exists_coherentInformation_maximizer N
  have he : Information.coherent N M ψ.state.marginalB = N.coherentInformation := by
    rw [← hc.coherentInformationFor_eq, ← hψ]
  exact ⟨ψ.state.marginalB, he, fun σ ↦ he ▸ hc.coherent_le_optimized σ⟩

end QuanIncapacity
