import QuanIncapacity.Framework.ArithmeticWeights
import QuanIncapacity.Framework.LogarithmicMean
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Integrated arithmetic inverse comparison

This is the arithmetic-integral form of the metric. Its identification with
the Kubo–Mori operator and with the relative-entropy Hessian is a separate
bridge; neither identification is assumed here.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open QIT MeasureTheory

namespace QuanIncapacity.MatrixSpace

variable {a b : Type*} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

theorem arithmetic_inverse_continuousOn {σ : CMatrix a} (hσ : σ.PosDef) :
    ContinuousOn (fun t : ℝ ↦ (arithmetic σ t)⁻¹) (Set.Icc 0 1) := by
  have hf : Continuous (arithmetic σ) := by
    unfold arithmetic
    fun_prop
  intro t ht
  have hu := (arithmetic_posDef hσ ht.1 ht.2).isUnit
  have hi : ContinuousAt Ring.inverse (arithmetic σ t) := by
    simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using
    (hi.comp hf.continuousAt).continuousWithinAt

theorem arithmetic_inverse_quadratic_continuousOn {σ : CMatrix a} (hσ : σ.PosDef)
    (x : a × a → ℂ) :
    ContinuousOn (fun t : ℝ ↦ quadratic (arithmetic σ t)⁻¹ x) (Set.Icc 0 1) := by
  have hi := arithmetic_inverse_continuousOn hσ
  unfold quadratic Matrix.mulVec dotProduct
  fun_prop

def arithmeticMetric (σ Z : CMatrix a) : ℝ :=
  ∫ t : ℝ in 0..1, quadratic (arithmetic σ t)⁻¹ (vec Z)

theorem arithmeticMetric_comparison {σ : CMatrix a} {ω : CMatrix b}
    (hσ : σ.PosDef) (hω : ω.PosDef) (J : MatrixMap a b)
    (hJ : ∀ Y, J Y.conjTranspose = (J Y).conjTranspose)
    (h : ∀ Y, ((J Y).conjTranspose * ω * J Y).trace.re ≤
      (Y.conjTranspose * σ * Y).trace.re) (Z : CMatrix b) :
    arithmeticMetric σ (hsAdjoint J Z) ≤ arithmeticMetric ω Z := by
  unfold arithmeticMetric
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
  · apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      arithmetic_inverse_quadratic_continuousOn hσ (vec (hsAdjoint J Z))
  · apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      arithmetic_inverse_quadratic_continuousOn hω (vec Z)
  · intro t ht
    have hp := arithmetic_inverse_comparison hσ hω J hJ h ht.1 ht.2
    have hn := (Complex.nonneg_iff.mp (hp.dotProduct_mulVec_nonneg (vec Z))).1
    have hq := Shadowing.quadratic_pullback (arithmetic σ t)⁻¹ (rep J).conjTranspose (vec Z)
    simp only [Matrix.conjTranspose_conjTranspose] at hq
    rw [Matrix.sub_mulVec, dotProduct_sub, hq, Complex.sub_re] at hn
    simpa only [quadratic, hsAdjoint, LinearMap.coe_mk, AddHom.coe_mk, vec_unvec] using
      sub_nonneg.mp hn

end QuanIncapacity.MatrixSpace
