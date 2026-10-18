import QuanIncapacity.Activation.DephasedErasureChannel
import QuanIncapacity.Framework.ChannelSimulation

/-! The abstract auxiliary channel is implemented by exactly `card c` uses
of the actual qutrit channel, with a pure encoder and a CPTP decoder. -/

noncomputable section
open QIT

namespace QuanIncapacity

theorem restrictedQubit_simulation : Simulates restrictedQubitChannel Λ := by
  refine ⟨⟨V, V_isometry⟩, qubitDecoder, ?_⟩
  exact (channel_comp_assoc qubitEncoder Λ qubitDecoder).symm

theorem dephasedErasure_fin_simulation (n : ℕ) :
    Simulates (DephasedErasure.channel (a := Fin n) (1 / 4) (1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (Λ.tensorPower n) := by
  apply Simulates.trans (P := restrictedQubitChannel.tensorPower n)
  · refine ⟨Excitation.encoder n, FlagDecoder.channel (Excitation.location n), ?_⟩
    rw [← channel_comp_assoc]
    apply channel_eq_of_map_eq
    exact (Excitation.encodedChannel_map n).trans (DephasedErasure.channel_map ..).symm
  · exact restrictedQubit_simulation.tensorPower n

variable {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]

theorem reindex_channel_single (v : a ≃ c) (i j : a) :
    (Channel.reindex v).map (Matrix.single i j 1) = Matrix.single (v i) (v j) 1 :=
  MatrixMap.ofReferenceIsometry_ofInjective_single v v.injective i j

theorem dephasedErasure_reindex (v : a ≃ c) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (Channel.reindex (Equiv.optionCongr v.symm)).comp
      ((DephasedErasure.channel q η hq0 hq1 hη0 hη1).comp (Channel.reindex v)) =
      DephasedErasure.channel q η hq0 hq1 hη0 hη1 := by
  apply channel_eq_of_map_eq
  have hs (i j : a) :
      ((Channel.reindex (Equiv.optionCongr v.symm)).comp
        ((DephasedErasure.channel q η hq0 hq1 hη0 hη1).comp (Channel.reindex v))).map
          (Matrix.single i j 1) =
        (DephasedErasure.channel q η hq0 hq1 hη0 hη1).map (Matrix.single i j 1) := by
    change (Channel.reindex _).map ((DephasedErasure.channel q η hq0 hq1 hη0 hη1).map
      ((Channel.reindex v).map (Matrix.single i j 1))) = _
    rw [reindex_channel_single, DephasedErasure.channel_map, DephasedErasure.channel_map]
    by_cases hij : i = j
    · subst j
      rw [DephasedErasure.map_diagonal, DephasedErasure.map_diagonal,
        map_add, map_smul, map_smul, reindex_channel_single, reindex_channel_single]
      simp [Equiv.optionCongr]
    · rw [DephasedErasure.map_off_diagonal _ _ _ _ (v.injective.ne hij),
        DephasedErasure.map_off_diagonal _ _ _ _ hij,
        map_smul, reindex_channel_single]
      simp [Equiv.optionCongr]
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single _ X, MatrixMap.map_eq_sum_single
    (DephasedErasure.channel q η hq0 hq1 hη0 hη1).map X]
  simp only [hs]

/-- The dimension is fixed after the finite private code is chosen. -/
theorem dephasedErasure_simulation (c : Type) [Fintype c] [DecidableEq c] :
    Simulates (DephasedErasure.channel (a := c) (1 / 4) (1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        (Λ.tensorPower (Fintype.card c)) := by
  apply Simulates.trans (P := DephasedErasure.channel (a := Fin (Fintype.card c))
    (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · refine ⟨ReferenceIsometry.ofEquiv (Fintype.equivFin c),
      Channel.reindex (Equiv.optionCongr (Fintype.equivFin c).symm), ?_⟩
    exact dephasedErasure_reindex (Fintype.equivFin c) _ _ _ _ _ _
  · exact dephasedErasure_fin_simulation _

end QuanIncapacity
