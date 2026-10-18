import QuanIncapacity.Framework.UnitaryMetric
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance

/-! Born probabilities of an actual spectral POVM and the variance of the
sample mean under the constructed IID product measure. -/

noncomputable section
open QIT MeasureTheory ProbabilityTheory Unitary QuanIncapacity.MatrixSpace
open scoped Matrix BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.ObservableStatistics

variable {a : Type} [Fintype a] [DecidableEq a]

def spectralPOVM (Y : CMatrix a) (hY : Y.IsHermitian) : POVM a a where
  effects i := conjugation hY.eigenvectorUnitary (Matrix.single i i 1)
  pos i := (posSemidef_single i).mul_mul_conjTranspose_same (hY.eigenvectorUnitary : CMatrix a)
  sum_eq_one := by
    rw [← map_sum]
    change conjugation hY.eigenvectorUnitary (∑ i, (POVM.coordinate a).effects i) = 1
    rw [(POVM.coordinate a).sum_eq_one]
    exact (conjStarAlgAut ℂ (CMatrix a) hY.eigenvectorUnitary).map_one

def weight (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) (i : a) : ℝ :=
  (conjugation (star hY.eigenvectorUnitary) ρ.matrix i i).re

theorem weight_nonneg (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) (i : a) :
    0 ≤ weight ρ Y hY i := by
  have hp : (conjugation (star hY.eigenvectorUnitary) ρ.matrix).PosSemidef :=
    ρ.pos.mul_mul_conjTranspose_same (star hY.eigenvectorUnitary : CMatrix a)
  exact (Complex.nonneg_iff.mp hp.diag_nonneg).1

theorem weight_sum (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) :
    ∑ i, weight ρ Y hY i = 1 := by
  change ∑ i, (conjugation (star hY.eigenvectorUnitary) ρ.matrix i i).re = 1
  rw [← Complex.re_sum]
  change (conjugation (star hY.eigenvectorUnitary) ρ.matrix).trace.re = 1
  rw [conjugation_trace, ρ.trace_re_eq_one]

theorem weight_born (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) (i : a) :
    weight ρ Y hY i = (ρ.matrix * (spectralPOVM Y hY).effects i).trace.re := by
  have h := conjugation_trace (star hY.eigenvectorUnitary)
    (ρ.matrix * conjugation hY.eigenvectorUnitary (Matrix.single i i 1))
  rw [conjugation_mul, conjugation_inverse] at h
  have hr := congrArg Complex.re h
  simpa [weight, spectralPOVM, Matrix.trace_mul_single] using hr

def distribution (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) : PMF a :=
  PMF.ofFintype (fun i ↦ ENNReal.ofReal (weight ρ Y hY i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ weight_nonneg ρ Y hY i), weight_sum]
    simp)

theorem distribution_toReal (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) (i : a) :
    (distribution ρ Y hY i).toReal = weight ρ Y hY i := by
  simp [distribution, ENNReal.toReal_ofReal (weight_nonneg ρ Y hY i)]

theorem moment (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) (k : ℕ) :
    ∑ i, weight ρ Y hY i * hY.eigenvalues i ^ k = (ρ.matrix * Y ^ k).trace.re := by
  let U := hY.eigenvectorUnitary
  have hd : conjugation (star U) Y = Matrix.diagonal (fun i ↦ (hY.eigenvalues i : ℂ)) := by
    calc
      _ = conjugation (star U)
          (conjugation U (Matrix.diagonal (fun i ↦ (hY.eigenvalues i : ℂ)))) :=
        congrArg (conjugation (star U)) hY.spectral_theorem
      _ = _ := conjugation_inverse U _
  have hp : conjugation (star U) (Y ^ k) =
      Matrix.diagonal (fun i ↦ ((hY.eigenvalues i ^ k : ℝ) : ℂ)) := by
    rw [show conjugation (star U) (Y ^ k) = (conjugation (star U) Y) ^ k from
      (conjStarAlgAut ℂ (CMatrix a) (star U)).map_pow Y k, hd, Matrix.diagonal_pow]
    ext i j
    simp [Matrix.diagonal_apply, Complex.ofReal_pow]
  have ht := congrArg Complex.re (conjugation_trace (star U) (ρ.matrix * Y ^ k))
  rw [conjugation_mul, hp] at ht
  simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Matrix.diagonal_apply_eq,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, weight] using ht

variable [MeasurableSpace a] [DiscreteMeasurableSpace a]

theorem born_mean (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) :
    (∫ i, hY.eigenvalues i ∂(distribution ρ Y hY).toMeasure) =
      (ρ.matrix * Y).trace.re := by
  rw [PMF.integral_eq_sum]
  simp only [distribution_toReal, smul_eq_mul]
  simpa only [pow_one] using moment ρ Y hY 1

theorem sample_mean_expectation (p : PMF a) (X : a → ℝ) (n : ℕ) (hn : 0 < n) :
    (∫ ω : Fin n → a, (n : ℝ)⁻¹ * ∑ i, X (ω i)
      ∂(Measure.pi (fun _ : Fin n ↦ p.toMeasure))) = ∫ i, X i ∂p.toMeasure := by
  have hX : Integrable X p.toMeasure := Integrable.of_finite
  have he (i : Fin n) : (∫ ω : Fin n → a, X (ω i)
      ∂(Measure.pi (fun _ : Fin n ↦ p.toMeasure))) = ∫ x, X x ∂p.toMeasure := by
    let hp := measurePreserving_eval (fun _ : Fin n ↦ p.toMeasure) i
    have hm : AEStronglyMeasurable X
        ((Measure.pi (fun _ : Fin n ↦ p.toMeasure)).map (Function.eval i)) := by
      rw [hp.map_eq]
      exact hX.aestronglyMeasurable
    simpa only [hp.map_eq] using (integral_map hp.measurable.aemeasurable hm).symm
  rw [integral_const_mul, integral_finsetSum]
  · simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hn), one_mul]
  · intro i _
    exact (measurePreserving_eval (fun _ : Fin n ↦ p.toMeasure) i).integrable_comp_of_integrable hX

theorem observable_sample_mean_expectation (ρ : State a) (Y : CMatrix a)
    (hY : Y.IsHermitian) (n : ℕ) (hn : 0 < n) :
    (∫ ω : Fin n → a, (n : ℝ)⁻¹ * ∑ i, hY.eigenvalues (ω i)
      ∂(Measure.pi (fun _ : Fin n ↦ (distribution ρ Y hY).toMeasure))) =
        (ρ.matrix * Y).trace.re := by
  rw [sample_mean_expectation _ _ n hn, born_mean]

theorem born_variance (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) :
    ProbabilityTheory.variance hY.eigenvalues (distribution ρ Y hY).toMeasure =
      Shadowing.variance ρ.matrix Y := by
  rw [variance_eq_sub (MemLp.of_discrete : MemLp hY.eigenvalues 2 _),
    PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp only [distribution_toReal, smul_eq_mul, Pi.pow_apply]
  rw [moment ρ Y hY 2]
  have hm := moment ρ Y hY 1
  simp only [pow_one] at hm
  rw [hm]
  simp only [Shadowing.variance, pow_two, Matrix.mul_assoc]

theorem sample_mean_variance (p : PMF a) (X : a → ℝ) (n : ℕ) (hn : 0 < n) :
    ProbabilityTheory.variance (fun ω : Fin n → a ↦ (n : ℝ)⁻¹ * ∑ i, X (ω i))
      (Measure.pi (fun _ : Fin n ↦ p.toMeasure)) =
        ProbabilityTheory.variance X p.toMeasure / n := by
  have hs : ProbabilityTheory.variance (fun ω : Fin n → a ↦ ∑ i, X (ω i))
      (Measure.pi (fun _ : Fin n ↦ p.toMeasure)) =
        (n : ℝ) * ProbabilityTheory.variance X p.toMeasure := by
    have hf : (∑ i : Fin n, fun ω : Fin n → a ↦ X (ω i)) =
        fun ω ↦ ∑ i, X (ω i) := by
      funext ω
      exact Finset.sum_apply ω _ _
    have h := variance_sum_pi (μ := fun _ : Fin n ↦ p.toMeasure)
      (X := fun _ : Fin n ↦ X) (fun _ ↦ MemLp.of_discrete)
    rw [hf] at h
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  rw [variance_const_mul, hs]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp

theorem observable_sample_mean (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian)
    (n : ℕ) (hn : 0 < n) :
    ProbabilityTheory.variance
      (fun ω : Fin n → a ↦ (n : ℝ)⁻¹ * ∑ i, hY.eigenvalues (ω i))
      (Measure.pi (fun _ : Fin n ↦ (distribution ρ Y hY).toMeasure)) =
        Shadowing.variance ρ.matrix Y / n := by
  rw [sample_mean_variance _ _ n hn, born_variance]

end QuanIncapacity.ObservableStatistics
