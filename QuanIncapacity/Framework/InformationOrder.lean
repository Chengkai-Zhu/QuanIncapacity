import QuanIncapacity.Framework.CompleteRelativeEntropy
import QuanIncapacity.Framework.PrivateCapacity
import QIT.Coding.Classical.HSWConverse
import QIT.Information.CQChannel

/-! Mutual-information and Holevo consequences of the complete relative-entropy order. -/

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators
open QIT

namespace QuanIncapacity

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem CompleteRelativeEntropyOrder.mutualInformation_le
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    {r : Type} [Fintype r] [DecidableEq r] [Nonempty r] (ρ : State (r × a)) :
    mutualInformation (((Channel.idChannel r).prod N).applyState ρ) ≤
      mutualInformation (((Channel.idChannel r).prod M).applyState ρ) := by
  have hh := h r ρ (ρ.marginalA.prod ρ.marginalB) ρ.matrix_supports_prod_marginals
  rw [State.applyState_prod_marginals, State.applyState_prod_marginals,
    State.relativeEntropy_prod_marginals_eq_mutualInformation,
    State.relativeEntropy_prod_marginals_eq_mutualInformation] at hh
  exact EReal.coe_le_coe_iff.mp hh

theorem applyState_id_prod_cqState {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Channel a b) (E : QIT.Ensemble ι a) :
    ((Channel.idChannel ι).prod N).applyState E.cqState = (Ensemble.mapChannel N E).cqState := by
  apply State.ext
  rw [applyState_id_prod_cqState_matrix]
  rfl

theorem CompleteRelativeEntropyOrder.holevo_le
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    {ι : Type} [Fintype ι] (E : QIT.Ensemble ι a) :
    (Ensemble.mapChannel N E).holevoInformation ≤ (Ensemble.mapChannel M E).holevoInformation := by
  classical
  haveI : Nonempty ι := E.cqState.nonempty.map Prod.fst
  have hh := h.mutualInformation_le E.cqState
  rwa [applyState_id_prod_cqState, applyState_id_prod_cqState,
    cqState_mutualInformation_eq_holevoInformation,
    cqState_mutualInformation_eq_holevoInformation] at hh

theorem CompleteRelativeEntropyOrder.privateInfo_nonpos
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    {ι : Type} [Fintype ι] (E : QIT.Ensemble ι a) : Information.privateInfo N M E ≤ 0 :=
  sub_nonpos.mpr (h.holevo_le E)

theorem zero_mem_privateValues [Nonempty a] (N : Channel a b) (M : Channel a e) :
    0 ∈ Information.privateValues N M := by
  let ρ := State.maximallyMixed a
  let E : QIT.Ensemble (Fin 1) a :=
    { probs := fun _ ↦ 1
      weights_sum := by simp
      states := fun _ ↦ ρ }
  have hz {c : Type} [Fintype c] [DecidableEq c] (Φ : Channel a c) :
      (Ensemble.mapChannel Φ E).holevoInformation = 0 := by
    rw [QIT.Ensemble.holevoInformation_def,
      QIT.Ensemble.averageState_of_constant (Ensemble.mapChannel Φ E) (Φ.applyState ρ)
        (fun _ ↦ rfl)]
    simp [E, Ensemble.mapChannel]
  exact ⟨1, E, by simp only [Information.privateInfo, hz, sub_self]⟩

theorem CompleteRelativeEntropyOrder.privateOneShot_eq_zero [Nonempty a]
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M) :
    Information.privateOneShot N M = 0 := by
  have hz := zero_mem_privateValues N M
  have hle : ∀ x ∈ Information.privateValues N M, x ≤ 0 := by
    rintro x ⟨k, E, rfl⟩
    exact h.privateInfo_nonpos E
  exact le_antisymm (csSup_le ⟨0, hz⟩ hle) (le_csSup ⟨0, hle⟩ hz)

end QuanIncapacity
