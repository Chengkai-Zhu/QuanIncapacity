import QuanIncapacity.Framework.RelativeEntropyHessian
import QuanIncapacity.Framework.MetricContinuity

/-! The affine-path integral formula for faithful relative entropy, in bits. -/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology
open QIT MeasureTheory QuanIncapacity.MatrixSpace

namespace QuanIncapacity.BKM

theorem integral_second_derivative_unit {f f' f'' : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f' (f'' t) t)
    (hf'' : ContinuousOn f'' (Set.Icc (0 : ℝ) 1)) :
    (∫ t : ℝ in 0..1, (1 - t) * f'' t) = f 1 - f 0 - f' 0 := by
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ ↦ (1 - s) * f' s + f s) ((1 - t) * f'' t) t := by
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    have hh := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul
      (hf' t ht')).add (hf t ht')
    convert hh using 1
    · rfl
    · dsimp; ring
  have hi : IntervalIntegrable (fun t : ℝ ↦ (1 - t) * f'' t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Pi.mul_def, Pi.sub_def] using (continuousOn_const.sub continuousOn_id).mul hf''
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp
  ring

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem affine_segment_posDef {ρ σ : CMatrix a} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : (σ + t • (ρ - σ)).PosDef := by
  have heq : σ + t • (ρ - σ) = (1 - t) • σ + t • ρ := by module
  rw [heq]
  by_cases h : t = 1
  · simpa [h] using hρ
  · exact (hσ.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 h))).add_posSemidef
      (hρ.posSemidef.smul ht.1)

theorem relativeEntropyNat_eq_integral [Nonempty a] {ρ σ : CMatrix a}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relativeEntropyNat ρ σ = (ρ - σ).trace.re +
      ∫ t : ℝ in 0..1, (1 - t) * arithmeticMetric (σ + t • (ρ - σ)) (ρ - σ) := by
  let X := ρ - σ
  let f : ℝ → ℝ := fun t ↦ relativeEntropyNat (σ + t • X) σ
  let f' : ℝ → ℝ := fun t ↦ (X * CFC.log (σ + t • X)).trace.re + X.trace.re -
    (X * CFC.log σ).trace.re
  let f'' : ℝ → ℝ := fun t ↦ arithmeticMetric (σ + t • X) X
  have hX : X.IsHermitian := hρ.isHermitian.sub hσ.isHermitian
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : (σ + t • X).PosDef :=
    affine_segment_posDef hρ hσ ht
  have hf (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt f (f' t) t :=
    relativeEntropyNat_hasDerivAt (hp t ht) hX
  have hf' (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt f' (f'' t) t := by
    simpa only [metric_eq_arithmeticMetric] using
      (relativeEntropyNat_hasDerivAt_derivative (τ := σ) (hp t ht) hX)
  have hc : ContinuousOn f'' (Set.Icc (0 : ℝ) 1) :=
    arithmeticMetric_continuousOn (by fun_prop) hp X
  have hh := integral_second_derivative_unit hf hf' hc
  have h0 : f 0 = 0 := by simp [f, relativeEntropyNat]
  have h1 : f 1 = relativeEntropyNat ρ σ := by simp [f, X]
  have hp0 : f' 0 = X.trace.re := by simp [f']
  rw [h0, h1, hp0] at hh
  dsimp [f''] at hh
  linarith

theorem relativeEntropy_eq_integral_of_posDef [Nonempty a] (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) :
    ρ.relativeEntropy σ =
      (((1 / Real.log 2) * ∫ t : ℝ in 0..1,
        (1 - t) * arithmeticMetric (σ.matrix + t • (ρ.matrix - σ.matrix))
          (ρ.matrix - σ.matrix) : ℝ) : EReal) := by
  rw [relativeEntropy_eq_nat_of_posDef ρ σ hρ hσ, relativeEntropyNat_eq_integral hρ hσ]
  simp only [Matrix.trace_sub, ρ.trace_eq_one, σ.trace_eq_one, sub_self, Complex.zero_re,
    zero_add, div_eq_mul_inv, one_mul, mul_comm]

end QuanIncapacity.BKM
