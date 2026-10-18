import QuanIncapacity.Framework.RelativeEntropyCriterion
import QIT.States.Schatten
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Support-aware logarithmic limits at singular positive semidefinite matrices. -/

noncomputable section
set_option maxHeartbeats 800000
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology BigOperators
open QIT MeasureTheory Filter Unitary QuanIncapacity.MatrixSpace

namespace QuanIncapacity.BKM

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem trace_mul_log_mono {ρ A B : CMatrix a} (hρ : ρ.PosSemidef)
    (hA : A.PosDef) (hAB : A ≤ B) :
    (ρ * CFC.log A).trace.re ≤ (ρ * CFC.log B).trace.re := by
  have hl := CFC.log_le_log hAB hA.isStrictlyPositive
  have hh := cMatrix_trace_mul_posSemidef_re_nonneg hρ (Matrix.le_iff.mp hl)
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hh

theorem trace_mul_conjugation_diagonal (ρ : CMatrix a)
    (U : Matrix.unitaryGroup a ℂ) (d : a → ℝ) :
    (ρ * conjugation U (Matrix.diagonal (fun i ↦ (d i : ℂ)))).trace.re =
      ∑ i, (conjugation (star U) ρ i i).re * d i := by
  rw [← conjugation_trace (star U) (ρ * conjugation U (Matrix.diagonal (fun i ↦ (d i : ℂ)))),
    conjugation_mul, conjugation_inverse]
  simp [Matrix.trace, Matrix.mul_diagonal, Complex.mul_re]

theorem log_affine_identity_spectral {σ : CMatrix a} (hσ : σ.IsHermitian) (s t : ℝ) :
    CFC.log (s • σ + t • (1 : CMatrix a)) =
      conjugation hσ.eigenvectorUnitary
        (Matrix.diagonal (fun i ↦ (Real.log (s * hσ.eigenvalues i + t) : ℂ))) := by
  let U := hσ.eigenvectorUnitary
  let eig := hσ.eigenvalues
  have hspec : σ = conjugation U (Matrix.diagonal (fun i ↦ (eig i : ℂ))) :=
    hσ.spectral_theorem
  have h1 : conjugation U 1 = 1 := (conjStarAlgAut ℂ (CMatrix a) U).map_one
  have heq : s • σ + t • (1 : CMatrix a) =
      conjugation U (Matrix.diagonal (fun i ↦ ((s * eig i + t : ℝ) : ℂ))) := by
    rw [hspec, ← h1, ← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower, ← map_add]
    congr 1
    ext i j
    by_cases h : i = j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, h, Complex.real_smul,
        Complex.ofReal_mul, Complex.ofReal_add]
  rw [heq, CFC.log]
  exact cfc_unitary_conj_diagonal_ofReal U (fun i ↦ s * eig i + t) Real.log

theorem trace_mul_log_identity_mix_tendsto {ρ σ : CMatrix a}
    (hσ : σ.PosSemidef) (hs : Matrix.Supports ρ σ) (c : ℝ) :
    Tendsto (fun ε : ℝ ↦
      (ρ * CFC.log ((1 - ε) • σ + (ε * c) • (1 : CMatrix a))).trace.re)
      (𝓝 0) (𝓝 (ρ * CFC.log σ).trace.re) := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let d : a → ℝ := fun i ↦ (conjugation (star U) ρ i i).re
  have heq (ε : ℝ) :
      (ρ * CFC.log ((1 - ε) • σ + (ε * c) • (1 : CMatrix a))).trace.re =
        ∑ i, d i * Real.log ((1 - ε) * eig i + ε * c) := by
    rw [log_affine_identity_spectral hσ.isHermitian, trace_mul_conjugation_diagonal]
  have hlim (i : a) : Tendsto (fun ε : ℝ ↦ d i * Real.log ((1 - ε) * eig i + ε * c))
      (𝓝 0) (𝓝 (d i * Real.log (eig i))) := by
    by_cases hi : eig i = 0
    · have hd : d i = 0 := by
        have hz := supports_conjugate_diagonal_re_eq_zero (M := ρ) (N := σ) hσ hs hi
        simpa only [d, U, conjugation_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_conjTranspose] using hz
      simp only [hd, zero_mul]
      exact tendsto_const_nhds
    · have hc : ContinuousAt (fun ε : ℝ ↦ Real.log ((1 - ε) * eig i + ε * c)) 0 :=
        Real.continuousAt_log (by simpa using hi) |>.comp (by fun_prop)
      simpa [Pi.mul_def] using (continuousAt_const.mul hc).tendsto
  have hh := tendsto_finsetSum Finset.univ (fun i _ ↦ hlim i)
  have hzero := heq 0
  simp only [sub_zero, one_smul, zero_mul, zero_smul, add_zero, one_mul] at hzero
  simpa only [← heq, ← hzero] using hh

theorem smul_trace_mul_log_identity_mix_tendsto {ρ σ : CMatrix a}
    (hσ : σ.PosSemidef) {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun ε : ℝ ↦ ε *
      (ρ * CFC.log ((1 - ε) • σ + (ε * c) • (1 : CMatrix a))).trace.re)
      (𝓝 0) (𝓝 0) := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let d : a → ℝ := fun i ↦ (conjugation (star U) ρ i i).re
  have heq (ε : ℝ) : ε *
      (ρ * CFC.log ((1 - ε) • σ + (ε * c) • (1 : CMatrix a))).trace.re =
        ∑ i, ε * (d i * Real.log ((1 - ε) * eig i + ε * c)) := by
    rw [log_affine_identity_spectral hσ.isHermitian, trace_mul_conjugation_diagonal,
      Finset.mul_sum]
  have hlim (i : a) : Tendsto
      (fun ε : ℝ ↦ ε * (d i * Real.log ((1 - ε) * eig i + ε * c))) (𝓝 0) (𝓝 0) := by
    by_cases hi : eig i = 0
    · have hh := ((Real.continuous_mul_log.comp
        (continuous_id.mul_const c)).div_const c).continuousAt.tendsto (x := (0 : ℝ))
      have heq' (ε : ℝ) : ε * (d i * Real.log ((1 - ε) * eig i + ε * c)) =
          d i * ((ε * c * Real.log (ε * c)) / c) := by
        rw [hi]
        field_simp [hc]
        ring
      simp_rw [heq']
      simpa [Pi.mul_def] using hh.const_mul (d i)
    · have hlog : ContinuousAt (fun ε : ℝ ↦ Real.log ((1 - ε) * eig i + ε * c)) 0 :=
        Real.continuousAt_log (by simpa using hi) |>.comp (by fun_prop)
      simpa [Pi.mul_def] using (continuousAt_id.mul (continuousAt_const.mul hlog)).tendsto
  have hh := tendsto_finsetSum Finset.univ (fun i _ ↦ hlim i)
  simpa only [← heq, Finset.sum_const_zero] using hh

theorem faithful_mix_posDef {σ τ : CMatrix a} (hσ : σ.PosSemidef) (hτ : τ.PosDef)
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) : ((1 - ε) • σ + ε • τ).PosDef :=
  Matrix.PosDef.posSemidef_add (hσ.smul (sub_nonneg.mpr hε.2.le)) (hτ.smul hε.1)

theorem exists_faithful_mix_bounds [Nonempty a] {σ τ : CMatrix a}
    (hσ : σ.PosSemidef) (hτ : τ.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ((1 - ε) • σ + (ε * c) • (1 : CMatrix a)).PosDef ∧
      (1 - ε) • σ + (ε * c) • (1 : CMatrix a) ≤ (1 - ε) • σ + ε • τ ∧
      (1 - ε) • σ + ε • τ ≤ (1 - ε) • σ + (ε * C) • (1 : CMatrix a) := by
  obtain ⟨c, hc, hle⟩ := (CFC.exists_pos_algebraMap_le_iff τ hτ.isHermitian).mpr
    (fun x hx ↦ hτ.isStrictlyPositive.spectrum_pos hx)
  let C := ‖τ‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hupper : τ ≤ C • (1 : CMatrix a) := by
    have hn : τ ≤ ‖τ‖ • (1 : CMatrix a) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        IsSelfAdjoint.le_algebraMap_norm_self τ hτ.isHermitian
    exact hn.trans (smul_le_smul_of_nonneg_right (by dsimp [C]; linarith)
      Matrix.PosSemidef.one.nonneg)
  refine ⟨c, hc, C, hC, fun ε hε ↦ ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.PosDef.posSemidef_add (hσ.smul (sub_nonneg.mpr hε.2.le))
      (Matrix.PosDef.one.smul (mul_pos hε.1 hc))
  · simpa only [Algebra.algebraMap_eq_smul_one, smul_smul] using
      add_le_add (le_refl ((1 - ε) • σ)) (smul_le_smul_of_nonneg_left hle hε.1.le)
  · simpa only [smul_smul] using
      add_le_add (le_refl ((1 - ε) • σ)) (smul_le_smul_of_nonneg_left hupper hε.1.le)

theorem trace_mul_log_faithful_mix_tendsto [Nonempty a] {ρ σ τ : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hτ : τ.PosDef)
    (hs : Matrix.Supports ρ σ) :
    Tendsto (fun ε : ℝ ↦ (ρ * CFC.log ((1 - ε) • σ + ε • τ)).trace.re)
      (𝓝[>] 0) (𝓝 (ρ * CFC.log σ).trace.re) := by
  obtain ⟨c, hc, C, hC, hb⟩ := exists_faithful_mix_bounds hσ hτ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((trace_mul_log_identity_mix_tendsto hσ hs c).mono_left nhdsWithin_le_nhds)
    ((trace_mul_log_identity_mix_tendsto hσ hs C).mono_left nhdsWithin_le_nhds)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    exact trace_mul_log_mono hρ (hb ε hε).1 (hb ε hε).2.1
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    exact trace_mul_log_mono hρ (faithful_mix_posDef hσ hτ hε) (hb ε hε).2.2

theorem smul_trace_mul_log_faithful_mix_tendsto [Nonempty a] {ρ σ τ : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hτ : τ.PosDef) :
    Tendsto (fun ε : ℝ ↦ ε * (ρ * CFC.log ((1 - ε) • σ + ε • τ)).trace.re)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨c, hc, C, hC, hb⟩ := exists_faithful_mix_bounds hσ hτ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((smul_trace_mul_log_identity_mix_tendsto (ρ := ρ) hσ (ne_of_gt hc)).mono_left
      nhdsWithin_le_nhds)
    ((smul_trace_mul_log_identity_mix_tendsto (ρ := ρ) hσ (ne_of_gt hC)).mono_left
      nhdsWithin_le_nhds)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    exact mul_le_mul_of_nonneg_left
      (trace_mul_log_mono hρ (hb ε hε).1 (hb ε hε).2.1) hε.1.le
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    exact mul_le_mul_of_nonneg_left
      (trace_mul_log_mono hρ (faithful_mix_posDef hσ hτ hε) (hb ε hε).2.2) hε.1.le

/-- Common faithful noise is allowed to be noncommuting with either endpoint. -/
theorem trace_mix_mul_log_mix_tendsto [Nonempty a] {ρ σ τ : CMatrix a}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hτ : τ.PosDef)
    (hs : Matrix.Supports ρ σ) :
    Tendsto (fun ε : ℝ ↦
      (((1 - ε) • ρ + ε • τ) * CFC.log ((1 - ε) • σ + ε • τ)).trace.re)
      (𝓝[>] 0) (𝓝 (ρ * CFC.log σ).trace.re) := by
  have hcross := trace_mul_log_faithful_mix_tendsto hρ hσ hτ hs
  have hnoise := smul_trace_mul_log_faithful_mix_tendsto hτ.posSemidef hσ hτ
  have heps : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
      : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝[>] 0) (𝓝 (1 - 0)))
  have hh := (heps.mul hcross).add hnoise
  simpa only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, one_mul, add_zero] using hh

end QuanIncapacity.BKM
