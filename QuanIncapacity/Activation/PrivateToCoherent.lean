import QuanIncapacity.Activation.ErasureBranches
import QuanIncapacity.Framework.ComplementaryAuxiliary

/-! The private-to-coherent-information inequality for an actual input and
the actual product channel. No entropy or activation bound is an assumption. -/

noncomputable section
open QIT
open scoped BigOperators

namespace QuanIncapacity.Activation

variable {r a b c e ι : Type} [Fintype r] [DecidableEq r]
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype e] [DecidableEq e]
variable [Fintype ι] [DecidableEq ι]

theorem traceAuxiliary_applyState (ρ : State (r × (a × c))) :
    ((Channel.idChannel r).prod (Channel.traceOutRight a c)).applyState ρ = dropAuxiliary ρ := by
  apply State.ext
  ext ⟨x, u⟩ ⟨y, v⟩
  change MatrixMap.kron (Channel.idChannel r).map (Channel.traceOutRight a c).map ρ.matrix (x, u) (y, v) = _
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  rfl

/-- The identity component contributes exactly `H(X|E)` for the constructed input. -/
theorem signalOutput_coherentInformation {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (E : Ensemble ι a) :
    (signalOutput N E).coherentInformation = (Ensemble.mapChannel M E).cqState.conditionalEntropy := by
  have hh := (hc.keepAuxiliary (c := Auxiliary E)).coherentInformationFor_eq_complement_conditionalEntropy
    (globalPurification E)
  have hm : ((Channel.idChannel ι).prod (M.comp (Channel.traceOutRight a (Auxiliary E)))).applyState
      (globalPurification E).state = (Ensemble.mapChannel M E).cqState := by
    rw [← amp_applyState_comp, traceAuxiliary_applyState, globalPurification_dropAuxiliary,
      applyState_id_prod_cqState]
  rw [hm] at hh
  exact hh

theorem middle_then_auxiliary {d : Type} [Fintype d] [DecidableEq d]
    (N : Channel a b) (T : Channel c d) (ρ : State (r × (a × c))) :
    ((Channel.idChannel r).prod ((Channel.idChannel b).prod T)).applyState
      (((Channel.idChannel r).prod (N.prod (Channel.idChannel c))).applyState ρ) =
        ((Channel.idChannel r).prod (N.prod T)).applyState ρ := by
  have hm : ((Channel.idChannel b).prod T).comp (N.prod (Channel.idChannel c)) = N.prod T := by
    apply channel_eq_of_map_eq
    apply LinearMap.ext
    intro X
    change MatrixMap.kron (Channel.idChannel b).map T.map
      (MatrixMap.kron N.map (Channel.idChannel c).map X) = MatrixMap.kron N.map T.map X
    have hh := MatrixMap.kron_comp_apply_general (Channel.idChannel b).map T.map N.map
      (Channel.idChannel c).map X
    rw [idChannel_map_eq, idChannel_map_eq, LinearMap.id_comp, LinearMap.comp_id] at hh
    simpa only [idChannel_map_eq] using hh
  rw [amp_applyState_comp, hm]

theorem output_signalOutput (N : Channel a b) (E : Ensemble ι a) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    DephasedErasure.output (signalOutput N E) q η hq0 hq1 hη0 hη1 =
      ((Channel.idChannel ι).prod
        (N.prod (DephasedErasure.channel q η hq0 hq1 hη0 hη1))).applyState (globalPurification E).state :=
  middle_then_auxiliary N (DephasedErasure.channel q η hq0 hq1 hη0 hη1) (globalPurification E).state

/-- Manuscript `lem:private-to-coherent`, including all parameter endpoints.
The auxiliary basis is `Σ x, support(ρ_x)`; `auxiliary_card` proves its dimension
is exactly `Σ x, rank(ρ_x)`. The reference is the quantum message register. -/
theorem private_to_coherent_bound {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (E : Ensemble ι a) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    q * η * (Ensemble.mapChannel M E).cqState.conditionalEntropy - q * binaryEntropy η -
        (1 - q) * (Ensemble.mapChannel N E).cqState.conditionalEntropy ≤
      (N.prod (DephasedErasure.channel q η hq0 hq1 hη0 hη1)).coherentInformationFor
        (globalPurification E) := by
  have hh := signalOutput_bound N E q η hq0 hq1 hη0 hη1
  rw [signalOutput_coherentInformation hc, output_signalOutput] at hh
  exact hh

end QuanIncapacity.Activation
