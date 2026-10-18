import QuanIncapacity.Framework.PrivateOptimization
import QuanIncapacity.Framework.CoherentProcessing
import QIT.Coding.Classical.HSWLimit

/-! General superadditivity, with actual product ensembles and appended states.
No complete-order hypothesis or coding theorem is used. -/
noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.Information
variable {a b e ι : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

omit [Nonempty a] in
private theorem mapChannel_eq_outputEnsemble [Fintype ι] [DecidableEq ι]
    (N : Channel a b) (E : QIT.Ensemble ι a) :
    Ensemble.mapChannel N E = N.outputEnsemble E := rfl

theorem privateInfo_relabelIndex [Fintype ι] [DecidableEq ι] {κ : Type}
    [Fintype κ] [DecidableEq κ] (N : Channel a b) (M : Channel a e)
    (E : QIT.Ensemble ι a) (v : κ ≃ ι) :
    privateInfo N M (E.relabelIndex v) = privateInfo N M E := by
  unfold privateInfo
  simp only [mapChannel_eq_outputEnsemble, Channel.outputEnsemble_relabelIndex,
    QIT.Ensemble.relabelIndex_holevoInformation]

theorem privateInfo_le_oneShot_finite [Fintype ι] [DecidableEq ι]
    (N : Channel a b) (M : Channel a e) (E : QIT.Ensemble ι a) :
    privateInfo N M E ≤ privateOneShot N M := by
  have h := privateInfo_le_oneShot N M (E.relabelIndex (Fintype.equivFin ι).symm)
  rw [privateInfo_relabelIndex] at h
  exact h

theorem privateInfo_append_prod {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (N : Channel a b) (M : Channel a e) (m n : ℕ)
    (E : QIT.Ensemble ι (QIT.TensorPower a m))
    (F : QIT.Ensemble κ (QIT.TensorPower a n)) :
    privateInfo (N.tensorPower (m + n)) (M.tensorPower (m + n))
      ((E.prod F).reindexStates (TensorPower.appendEquiv a m n)) =
      privateInfo (N.tensorPower m) (M.tensorPower m) E +
        privateInfo (N.tensorPower n) (M.tensorPower n) F := by
  unfold privateInfo
  change (N.tensorPower (m + n)).hswHolevoRate _ -
    (M.tensorPower (m + n)).hswHolevoRate _ = _
  rw [Channel.hswHolevoRate_append_prod_reindex,
    Channel.hswHolevoRate_append_prod_reindex]
  unfold Channel.hswHolevoRate
  simp only [mapChannel_eq_outputEnsemble]
  ring

theorem private_superadditive (N : Channel a b) (M : Channel a e) (m n : ℕ) :
    privateOneShot (N.tensorPower m) (M.tensorPower m) +
      privateOneShot (N.tensorPower n) (M.tensorPower n) ≤
        privateOneShot (N.tensorPower (m + n)) (M.tensorPower (m + n)) := by
  haveI : Nonempty (QIT.TensorPower a m) := tensorPower_nonempty_of_nonempty _
  haveI : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty _
  haveI : Nonempty (QIT.TensorPower a (m + n)) := tensorPower_nonempty_of_nonempty _
  rw [le_iff_forall_pos_lt_add]
  intro η hη
  obtain ⟨x, ⟨k, E, rfl⟩, hE⟩ := exists_lt_of_lt_csSup
    (show (privateValues (N.tensorPower m) (M.tensorPower m)).Nonempty from
      ⟨0, zero_mem_privateValues _ _⟩)
    (show privateOneShot (N.tensorPower m) (M.tensorPower m) - η / 4 <
      sSup (privateValues (N.tensorPower m) (M.tensorPower m)) by
      change _ < privateOneShot _ _; linarith)
  obtain ⟨x, ⟨l, F, rfl⟩, hF⟩ := exists_lt_of_lt_csSup
    (show (privateValues (N.tensorPower n) (M.tensorPower n)).Nonempty from
      ⟨0, zero_mem_privateValues _ _⟩)
    (show privateOneShot (N.tensorPower n) (M.tensorPower n) - η / 4 <
      sSup (privateValues (N.tensorPower n) (M.tensorPower n)) by
      change _ < privateOneShot _ _; linarith)
  have hG := privateInfo_le_oneShot_finite (N.tensorPower (m + n))
    (M.tensorPower (m + n)) ((E.prod F).reindexStates (TensorPower.appendEquiv a m n))
  rw [privateInfo_append_prod] at hG
  linarith

end Information

variable {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem ComplementaryChannels.coherent_le_optimized {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (ρ : State a) :
    Information.coherent N M ρ ≤ N.coherentInformation := by
  have h := N.coherentInformationFor_le ρ.canonicalPurification
  rw [hc.coherentInformationFor_eq] at h
  simpa only [show ρ.canonicalPurification.state.marginalB = ρ from
    State.ext ρ.canonicalPurification_purifies] using h

theorem coherent_append_prod (N : Channel a b) (M : Channel a e) (m n : ℕ)
    (ρ : State (QIT.TensorPower a m)) (σ : State (QIT.TensorPower a n)) :
    Information.coherent (N.tensorPower (m + n)) (M.tensorPower (m + n))
      ((ρ.prod σ).reindex (TensorPower.appendEquiv a m n)) =
      Information.coherent (N.tensorPower m) (M.tensorPower m) ρ +
        Information.coherent (N.tensorPower n) (M.tensorPower n) σ := by
  unfold Information.coherent
  rw [Channel.tensorPower_append_applyState_prod, Channel.tensorPower_append_applyState_prod]
  simp only [State.vonNeumann_reindex, State.vonNeumann_prod]
  ring

theorem coherent_superadditive (N : Channel a b) (m n : ℕ) :
    (N.tensorPower m).coherentInformation + (N.tensorPower n).coherentInformation ≤
      (N.tensorPower (m + n)).coherentInformation := by
  obtain ⟨M, hc⟩ := exists_complementaryChannel N
  haveI : Nonempty (QIT.TensorPower a m) := tensorPower_nonempty_of_nonempty _
  haveI : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty _
  haveI : Nonempty (QIT.TensorPower a (m + n)) := tensorPower_nonempty_of_nonempty _
  rw [le_iff_forall_pos_lt_add]
  intro η hη
  obtain ⟨x, ⟨ψ, rfl⟩, hψ⟩ := exists_lt_of_lt_csSup
    (N.tensorPower m).coherentInformationValues_nonempty
    (show (N.tensorPower m).coherentInformation - η / 4 <
      sSup (N.tensorPower m).coherentInformationValues by
      change _ < (N.tensorPower m).coherentInformation; linarith)
  obtain ⟨x, ⟨φ, rfl⟩, hφ⟩ := exists_lt_of_lt_csSup
    (N.tensorPower n).coherentInformationValues_nonempty
    (show (N.tensorPower n).coherentInformation - η / 4 <
      sSup (N.tensorPower n).coherentInformationValues by
      change _ < (N.tensorPower n).coherentInformation; linarith)
  have hG := (hc.tensorPower (m + n)).coherent_le_optimized
    ((ψ.state.marginalB.prod φ.state.marginalB).reindex (TensorPower.appendEquiv a m n))
  rw [coherent_append_prod, ← (hc.tensorPower m).coherentInformationFor_eq,
    ← (hc.tensorPower n).coherentInformationFor_eq] at hG
  linarith

end QuanIncapacity
