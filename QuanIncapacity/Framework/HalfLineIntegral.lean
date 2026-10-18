import QuanIncapacity.Framework.LogarithmicMean
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The scalar half-line resolvent integral, including coincident positive
eigenvalues. Integrability follows from a nonnegative derivative and its
finite limit, rather than from an additional analytic premise. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace QuanIncapacity.BKM

def halfLinePrimitive (x y s : ℝ) : ℝ :=
  if x = y then -(s + x)⁻¹ else (Real.log (s + y) - Real.log (s + x)) / (x - y)

theorem halfLinePrimitive_derivative {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (s : ℝ) (hs : s ∈ Ici 0) :
    HasDerivAt (halfLinePrimitive x y) ((s + x)⁻¹ * (s + y)⁻¹) s := by
  have hs0 : 0 ≤ s := hs
  have hsx : s + x ≠ 0 := ne_of_gt (by linarith [hs] : 0 < s + x)
  have hsy : s + y ≠ 0 := ne_of_gt (by linarith [hs] : 0 < s + y)
  by_cases hxy : x = y
  · subst y
    have he : halfLinePrimitive x x = fun t ↦ -(t + x)⁻¹ := by
      funext t
      exact if_pos rfl
    rw [he]
    convert (((hasDerivAt_id s).add_const x).inv hsx).neg using 1
    · funext t
      simp only [id_eq]
      congr 1
    · simp only [neg_neg, id_eq]
      field_simp
  · have he : halfLinePrimitive x y =
        fun t ↦ (Real.log (t + y) - Real.log (t + x)) / (x - y) := by
      funext t
      exact if_neg hxy
    rw [he]
    convert ((((hasDerivAt_id s).add_const y).log hsy).sub
      (((hasDerivAt_id s).add_const x).log hsx)).div_const (x - y) using 1
    · funext t
      simp only [id_eq, Pi.sub_apply]
    · simp only [id_eq]
      field_simp [hsx, hsy, sub_ne_zero.mpr hxy]
      ring

theorem log_shift_difference_tendsto {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (fun s : ℝ ↦ Real.log (s + y) - Real.log (s + x)) atTop (𝓝 0) := by
  have hi : Tendsto (fun s : ℝ ↦ (s + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ x tendsto_id)
  have hr : Tendsto (fun s : ℝ ↦ (s + y) / (s + x)) atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℝ ↦ 1) atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
    have h := hc.add (hi.const_mul (y - x))
    have h' : Tendsto (fun s : ℝ ↦ 1 + (y - x) * (s + x)⁻¹) atTop (𝓝 1) := by
      simpa using h
    apply h'.congr'
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    have hs0 : 0 < s := hs
    field_simp [ne_of_gt (by linarith : 0 < s + x)]
    ring
  have hl : Tendsto (fun s : ℝ ↦ Real.log ((s + y) / (s + x))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  apply hl.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  have hs0 : 0 < s := hs
  exact Real.log_div (ne_of_gt (by linarith : 0 < s + y))
    (ne_of_gt (by linarith : 0 < s + x))

theorem halfLinePrimitive_tendsto {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Tendsto (halfLinePrimitive x y) atTop (𝓝 0) := by
  by_cases hxy : x = y
  · subst y
    have he : halfLinePrimitive x x = fun t ↦ -(t + x)⁻¹ := by
      funext t
      exact if_pos rfl
    rw [he]
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ x tendsto_id)).neg
  · have he : halfLinePrimitive x y =
        fun t ↦ (Real.log (t + y) - Real.log (t + x)) / (x - y) := by
      funext t
      exact if_neg hxy
    rw [he]
    simpa using (log_shift_difference_tendsto hx hy).div_const (x - y)

theorem halfLine_resolvent_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun s : ℝ ↦ (s + x)⁻¹ * (s + y)⁻¹) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (halfLinePrimitive_derivative hx hy)
    (fun s hs ↦ by have hs0 : 0 < s := hs; positivity) (halfLinePrimitive_tendsto hx hy)

theorem integral_halfLine_resolvent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ s : ℝ in Ioi 0, (s + x)⁻¹ * (s + y)⁻¹) = inverseLogMean x y := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (halfLinePrimitive_derivative hx hy)
    (fun s hs ↦ by have hs0 : 0 < s := hs; positivity) (halfLinePrimitive_tendsto hx hy)]
  by_cases hxy : x = y
  · simp [halfLinePrimitive, inverseLogMean, hxy]
  · simp only [halfLinePrimitive, inverseLogMean, ite_eq_right hxy, zero_add, zero_sub]
    ring

end QuanIncapacity.BKM
