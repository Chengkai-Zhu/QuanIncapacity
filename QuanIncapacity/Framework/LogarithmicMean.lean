import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Scalar inverse logarithmic mean

The diagonal case is included explicitly. Consequently the arithmetic
integral remains valid for repeated eigenvalues, including the diagonal
matrix units of a faithful density matrix.
-/

noncomputable section
open MeasureTheory

namespace QuanIncapacity.BKM

def inverseLogMean (x y : ℝ) : ℝ :=
  if x = y then x⁻¹ else (Real.log x - Real.log y) / (x - y)

theorem integral_arithmetic_inverse {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in 0..1, ((1 - t) * x + t * y)⁻¹) = inverseLogMean x y := by
  by_cases hxy : x = y
  · subst y
    have hc : (fun t : ℝ ↦ ((1 - t) * x + t * x)⁻¹) = fun _ ↦ x⁻¹ := by
      funext t
      congr 1
      ring
    rw [hc]
    simp [inverseLogMean]
  · have hc : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have hfun : (fun t : ℝ ↦ ((1 - t) * x + t * y)⁻¹) =
        fun t ↦ ((y - x) * t + x)⁻¹ := by
      funext t
      congr 1
      ring
    rw [hfun, intervalIntegral.integral_comp_mul_add (fun s : ℝ ↦ s⁻¹) hc x]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    rw [integral_inv_of_pos hx hy, Real.log_div (ne_of_gt hy) (ne_of_gt hx)]
    simp only [inverseLogMean, ite_eq_right hxy, smul_eq_mul]
    field_simp
    ring

theorem arithmetic_eigenvalue_pos {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < (1 - t) * x + t * y := by
  by_cases ht : t = 1
  · simpa [ht] using hy
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hx)
      (mul_nonneg ht0 hy.le)

theorem continuousOn_arithmetic_inverse {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ContinuousOn (fun t : ℝ ↦ ((1 - t) * x + t * y)⁻¹) (Set.Icc 0 1) := by
  apply ContinuousOn.inv₀
  · fun_prop
  · intro t ht
    exact ne_of_gt (arithmetic_eigenvalue_pos hx hy ht.1 ht.2)

theorem inverseLogMean_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < inverseLogMean x y := by
  by_cases hxy : x = y
  · simp [inverseLogMean, hxy, hy]
  · rw [inverseLogMean, ite_eq_right hxy]
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (Real.log_lt_log hx hlt))
        (sub_neg.mpr hlt)
    · exact div_pos (sub_pos.mpr (Real.log_lt_log hy hgt)) (sub_pos.mpr hgt)

def logMean (x y : ℝ) : ℝ := (inverseLogMean x y)⁻¹

theorem integral_geometric {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ s : ℝ in 0..1, x ^ s * y ^ (1 - s)) = logMean x y := by
  by_cases hxy : x = y
  · subst y
    have hf : (fun s : ℝ ↦ x ^ s * x ^ (1 - s)) = fun _ ↦ x := by
      funext s
      rw [← Real.rpow_add hx]
      simp
    rw [hf]
    simp [logMean, inverseLogMean]
  · have hlog : Real.log x - Real.log y ≠ 0 := by
      intro h
      exact hxy (Real.strictMonoOn_log.injOn hx hy (sub_eq_zero.mp h))
    have hf : (fun s : ℝ ↦ x ^ s * y ^ (1 - s)) =
        fun s ↦ y * Real.exp ((Real.log x - Real.log y) * s) := by
      funext s
      rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, ← Real.exp_add]
      rw [show Real.log x * s + Real.log y * (1 - s) =
        Real.log y + (Real.log x - Real.log y) * s by ring, Real.exp_add, Real.exp_log hy]
    rw [hf, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left Real.exp hlog]
    simp only [mul_zero, mul_one, integral_exp, Real.exp_zero, Real.exp_sub,
      Real.exp_log hx, Real.exp_log hy, smul_eq_mul]
    simp only [logMean, inverseLogMean, ite_eq_right hxy, inv_div]
    field_simp

end QuanIncapacity.BKM
