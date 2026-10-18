import QuanIncapacity.Framework.ObservableStatistics
import QuanIncapacity.Framework.ArithmeticCriterion

/-! The statistical meaning of complete observable shadowing, using the
actual Born laws and constructed independent copies on both outputs. -/

noncomputable section
open QIT MeasureTheory QuanIncapacity.MatrixSpace
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.ObservableStatistics

variable {a : Type} [Fintype a] [DecidableEq a]
variable [MeasurableSpace a] [DiscreteMeasurableSpace a]

def sampleMeanExpectation (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian)
    (n : ℕ) : ℝ :=
  ∫ ω : Fin n → a, (n : ℝ)⁻¹ * ∑ i, hY.eigenvalues (ω i)
    ∂(Measure.pi (fun _ : Fin n ↦ (distribution ρ Y hY).toMeasure))

theorem sampleMeanExpectation_eq (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian)
    (n : ℕ) (hn : 0 < n) :
    sampleMeanExpectation ρ Y hY n = (ρ.matrix * Y).trace.re :=
  observable_sample_mean_expectation ρ Y hY n hn

def sampleMeanVariance (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian) (n : ℕ) : ℝ :=
  ProbabilityTheory.variance
    (fun ω : Fin n → a ↦ (n : ℝ)⁻¹ * ∑ i, hY.eigenvalues (ω i))
    (Measure.pi (fun _ : Fin n ↦ (distribution ρ Y hY).toMeasure))

theorem sampleMeanVariance_eq (ρ : State a) (Y : CMatrix a) (hY : Y.IsHermitian)
    (n : ℕ) (hn : 0 < n) : sampleMeanVariance ρ Y hY n = Shadowing.variance ρ.matrix Y / n :=
  observable_sample_mean ρ Y hY n hn

end QuanIncapacity.ObservableStatistics

namespace QuanIncapacity.Shadowing

variable {a b e r : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype e] [DecidableEq e] [Fintype r] [DecidableEq r]

theorem amplified_observable_hermitian {N : Channel a b} {M : Channel a e}
    {J : MatrixMap b e} (h : IsUnbiasedShadow N.map M.map J)
    (Y : CMatrix (r × b)) (hY : Y.IsHermitian) : (amp r J Y).IsHermitian := by
  exact (amp_map_adjoint (r := r) J h.map_adjoint Y).symm.trans
    (congrArg (amp r J) hY.eq)

variable [MeasurableSpace (r × b)] [DiscreteMeasurableSpace (r × b)]
variable [MeasurableSpace (r × e)] [DiscreteMeasurableSpace (r × e)]

theorem shadow_sample_mean_unbiased {N : Channel a b} {M : Channel a e}
    {J : MatrixMap b e} (h : IsUnbiasedShadow N.map M.map J) (ρ : State (r × a))
    (Y : CMatrix (r × b)) (hY : Y.IsHermitian) (n : ℕ) (hn : 0 < n) :
    ObservableStatistics.sampleMeanExpectation (((Channel.idChannel r).prod M).applyState ρ)
      (amp r J Y) (amplified_observable_hermitian h Y hY) n =
    ObservableStatistics.sampleMeanExpectation (((Channel.idChannel r).prod N).applyState ρ)
      Y hY n := by
  rw [ObservableStatistics.sampleMeanExpectation_eq _ _ _ n hn,
    ObservableStatistics.sampleMeanExpectation_eq _ _ _ n hn]
  exact (congrArg Complex.re (h.amp_mean_eq ρ.matrix Y)).symm

/-- Joint reference observables, arbitrary entangled inputs and any positive
number of independent copies. The estimator variance is at most the
receiver estimator variance, with the exact `1/n` statistical factor. -/
theorem complete_shadow_sample_mean {N : Channel a b} {M : Channel a e} {J : MatrixMap b e}
    (h : IsCompleteShadow N.map M.map J) (ρ : State (r × a))
    (Y : CMatrix (r × b)) (hY : Y.IsHermitian) (n : ℕ) (hn : 0 < n) :
    ObservableStatistics.sampleMeanVariance (((Channel.idChannel r).prod M).applyState ρ)
      (amp r J Y) (amplified_observable_hermitian h.1 Y hY) n ≤
    ObservableStatistics.sampleMeanVariance (((Channel.idChannel r).prod N).applyState ρ)
      Y hY n := by
  rw [ObservableStatistics.sampleMeanVariance_eq _ _ _ n hn,
    ObservableStatistics.sampleMeanVariance_eq _ _ _ n hn]
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast hn.le)
  exact h.2 r ρ Y hY

end QuanIncapacity.Shadowing
