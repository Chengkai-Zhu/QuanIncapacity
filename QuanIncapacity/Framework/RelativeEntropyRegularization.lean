import QuanIncapacity.Framework.LogBoundary
import QIT.Information.Renyi.SandwichedRenyiOptimizedUSC

/-!
# Common-state regularization of supported relative entropy

The proof uses operator-log monotonicity and explicit spectral bounds. This
establishes the boundary limit directly, without adding joint convexity or
lower semicontinuity as theorem assumptions. The common noise need not commute
with either state.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology
open QIT MeasureTheory Filter

namespace QuanIncapacity.BKM

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem relativeEntropy_eq_trace_of_supports (ρ σ : State a)
    (hs : Matrix.Supports ρ.matrix σ.matrix) :
    ρ.relativeEntropy σ =
      ((-ρ.vonNeumann - (ρ.matrix * CFC.log σ.matrix).trace.re / Real.log 2 : ℝ) : EReal) := by
  rw [State.relativeEntropy_eq_coe_of_supports ρ σ hs]
  congr 1
  unfold State.relativeEntropyPSDReferenceTraceLogFinite
  dsimp only
  rw [State.relativeEntropyTraceLog_vonNeumann_psdSupportCompressedState_eq ρ σ.pos hs]
  have ht := State.relativeEntropyTraceLog_trace_mul_psdSupportLog_eq_trace_mul_cfc_logZero
    ρ σ.pos hs
  have hf : (fun x : ℝ ↦ if x = 0 then 0 else Real.log x) = Real.log := by
    funext x
    by_cases h : x = 0 <;> simp [h]
  rw [hf] at ht
  change -ρ.vonNeumann -
    (psdSupportCompress σ.matrix σ.pos ρ.matrix *
      State.psdLog (psdSupportCompress σ.matrix σ.pos σ.matrix)
        (psdSupportCompress_self_posDef σ.matrix σ.pos)).trace.re / Real.log 2 = _
  rw [ht]
  rfl

theorem fullRankApproxStatePath_matrix (ρ τ : State a) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    (State.fullRankApproxStatePath ρ τ ε).matrix = (1 - ε) • ρ.matrix + ε • τ.matrix := by
  rw [State.fullRankApproxStatePath_eq_of_mem ρ τ hε, State.fullRankApproxState_matrix]
  ext i j
  simp [State.fullRankApproxMatrix, State.regularizedStateMatrix, Complex.real_smul,
    Matrix.smul_apply]

theorem relativeEntropy_common_regularization_tendsto [Nonempty a]
    (ρ σ τ : State a) (hτ : τ.matrix.PosDef)
    (hs : Matrix.Supports ρ.matrix σ.matrix) :
    Tendsto (fun ε : ℝ ↦
      (State.fullRankApproxStatePath ρ τ ε).relativeEntropy
        (State.fullRankApproxStatePath σ τ ε))
      (𝓝[Set.Ioo 0 1] 0) (𝓝 (ρ.relativeEntropy σ)) := by
  let ρp := State.fullRankApproxStatePath ρ τ
  let σp := State.fullRankApproxStatePath σ τ
  have hmatrix : ∀ᶠ ε in 𝓝[Set.Ioo (0 : ℝ) 1] 0,
      (ρp ε).matrix = (1 - ε) • ρ.matrix + ε • τ.matrix ∧
      (σp ε).matrix = (1 - ε) • σ.matrix + ε • τ.matrix := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ⟨fullRankApproxStatePath_matrix ρ τ hε, fullRankApproxStatePath_matrix σ τ hε⟩
  have hcross : Tendsto (fun ε : ℝ ↦ ((ρp ε).matrix * CFC.log (σp ε).matrix).trace.re)
      (𝓝[Set.Ioo 0 1] 0) (𝓝 (ρ.matrix * CFC.log σ.matrix).trace.re) := by
    have hh := (trace_mix_mul_log_mix_tendsto ρ.pos σ.pos hτ hs).mono_left
      (nhdsWithin_mono (0 : ℝ) (show Set.Ioo 0 1 ⊆ Set.Ioi 0 from fun _ h ↦ h.1))
    apply hh.congr'
    filter_upwards [hmatrix] with ε hε
    rw [hε.1, hε.2]
  have hentropy : Tendsto (fun ε : ℝ ↦ (ρp ε).vonNeumann)
      (𝓝[Set.Ioo 0 1] 0) (𝓝 ρ.vonNeumann) :=
    State.vonNeumann_continuous.tendsto ρ |>.comp (State.fullRankApproxStatePath_tendsto_zero ρ τ)
  have hfinite := hentropy.neg.sub (hcross.div_const (Real.log 2))
  rw [relativeEntropy_eq_trace_of_supports ρ σ hs]
  have hcoe := (continuous_coe_real_ereal.tendsto _).comp hfinite
  apply hcoe.congr'
  filter_upwards [State.fullRankApproxStatePath_eventually_posDef_of_noise σ τ hτ] with ε hε
  exact (relativeEntropy_eq_trace_of_supports (ρp ε) (σp ε)
    (Matrix.Supports.of_right_posDef _ _ hε)).symm

end QuanIncapacity.BKM
