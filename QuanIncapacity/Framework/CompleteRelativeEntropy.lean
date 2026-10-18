import QuanIncapacity.Framework.RelativeEntropyRegularization

/-! Complete relative-entropy comparison, including supported singular input states. -/

noncomputable section
open scoped ComplexOrder MatrixOrder Topology
open QIT Filter QuanIncapacity.MatrixSpace

namespace QuanIncapacity

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem applyState_fullRankApproxStatePath (N : Channel a b) (ρ τ : State a) (ε : ℝ) :
    N.applyState (State.fullRankApproxStatePath ρ τ ε) =
      State.fullRankApproxStatePath (N.applyState ρ) (N.applyState τ) ε := by
  by_cases hε : ε ∈ Set.Ioo (0 : ℝ) 1
  · apply State.ext
    rw [BKM.fullRankApproxStatePath_matrix (N.applyState ρ) (N.applyState τ) hε]
    change N.map (State.fullRankApproxStatePath ρ τ ε).matrix = _
    rw [BKM.fullRankApproxStatePath_matrix ρ τ hε, map_add,
      LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]
    rfl
  · simp [State.fullRankApproxStatePath, hε]

/-- `M` dominates `N` for every reference and every support-compatible input pair. -/
def CompleteRelativeEntropyOrder (N : Channel a b) (M : Channel a e) : Prop :=
  ∀ (r : Type) [Fintype r] [DecidableEq r] [Nonempty r],
    ∀ ρ σ : State (r × a), Matrix.Supports ρ.matrix σ.matrix →
      (((Channel.idChannel r).prod N).applyState ρ).relativeEntropy
          (((Channel.idChannel r).prod N).applyState σ) ≤
        (((Channel.idChannel r).prod M).applyState ρ).relativeEntropy
          (((Channel.idChannel r).prod M).applyState σ)

theorem CompleteBKMOrder.relativeEntropyOrder [Nonempty a] [Nonempty b] [Nonempty e]
    {N : Channel a b} {M : Channel a e}
    {hN : (N.map 1).PosDef} {hM : (M.map 1).PosDef} (h : CompleteBKMOrder N M hN hM) :
    CompleteRelativeEntropyOrder N M := by
  intro r _ _ _ ρ σ hs
  let NR := (Channel.idChannel r).prod N
  let MR := (Channel.idChannel r).prod M
  let τ := State.maximallyMixed (r × a)
  have hτ : τ.matrix.PosDef := State.maximallyMixed_posDef
  have hNτ : (NR.applyState τ).matrix.PosDef := amp_posDef N hN hτ
  have hMτ : (MR.applyState τ).matrix.PosDef := amp_posDef M hM hτ
  have hNs : Matrix.Supports (NR.applyState ρ).matrix (NR.applyState σ).matrix :=
    State.channel_map_supports NR σ.pos hs
  have hMs : Matrix.Supports (MR.applyState ρ).matrix (MR.applyState σ).matrix :=
    State.channel_map_supports MR σ.pos hs
  have hlimN := BKM.relativeEntropy_common_regularization_tendsto
    (NR.applyState ρ) (NR.applyState σ) (NR.applyState τ) hNτ hNs
  have hlimM := BKM.relativeEntropy_common_regularization_tendsto
    (MR.applyState ρ) (MR.applyState σ) (MR.applyState τ) hMτ hMs
  haveI : (𝓝[Set.Ioo (0 : ℝ) 1] 0).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0 : ℝ) < 1)]
    infer_instance
  apply le_of_tendsto_of_tendsto hlimN hlimM
  filter_upwards [State.fullRankApproxStatePath_eventually_posDef_of_noise ρ τ hτ,
    State.fullRankApproxStatePath_eventually_posDef_of_noise σ τ hτ] with ε hρε hσε
  simpa only [applyState_fullRankApproxStatePath] using
    h.relativeEntropy_le_of_posDef r
      (State.fullRankApproxStatePath ρ τ ε) (State.fullRankApproxStatePath σ τ ε) hρε hσε

theorem Shadowing.complete_relativeEntropy_order [Nonempty a] [Nonempty b] [Nonempty e]
    (N : Channel a b) (M : Channel a e) (J : MatrixMap b e)
    (h : Shadowing.IsCompleteShadow N.map M.map J)
    (hN : (N.map 1).PosDef) (hM : (M.map 1).PosDef) : CompleteRelativeEntropyOrder N M :=
  (Shadowing.completeBKMOrder N M J h hN hM).relativeEntropyOrder

end QuanIncapacity
