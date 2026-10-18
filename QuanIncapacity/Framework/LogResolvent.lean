import QuanIncapacity.Framework.KuboMoriIntegral
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Compact resolvent formulas for the logarithm

All logarithms in this module are natural. The interval `[0,1]` includes both
endpoints; the equal-eigenvalue case is proved separately, without a spectral gap.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open QIT MeasureTheory Unitary QuanIncapacity.MatrixSpace

namespace QuanIncapacity.BKM

theorem integral_log_resolvent {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in 0..1, (x - 1) * ((1 - t) + t * x)⁻¹) = Real.log x := by
  rw [intervalIntegral.integral_const_mul]
  have hi := integral_arithmetic_inverse (x := 1) (by norm_num) hx
  simp only [mul_one] at hi
  rw [hi]
  by_cases h : x = 1
  · simp [h]
  · simp only [inverseLogMean, ite_eq_right (Ne.symm h), Real.log_one, zero_sub]
    field_simp
    ring

theorem integral_resolvent_product {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in 0..1,
      ((1 - t) + t * x)⁻¹ * ((1 - t) + t * y)⁻¹) = inverseLogMean x y := by
  have hp {z : ℝ} (hz : 0 < z) (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      0 < (1 - t) + t * z := by
    simpa only [mul_one] using arithmetic_eigenvalue_pos (x := 1) (by norm_num) hz
      (by simpa using ht.1) (by simpa using ht.2)
  have hc {z : ℝ} (hz : 0 < z) :
      ContinuousOn (fun t : ℝ ↦ ((1 - t) + t * z)⁻¹) (Set.uIcc 0 1) := by
    simpa using continuousOn_arithmetic_inverse (x := 1) (by norm_num) hz
  by_cases hxy : x = y
  · subst y
    have hd (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
        HasDerivAt (fun s : ℝ ↦ s / ((1 - s) + s * x))
          (((1 - t) + t * x)⁻¹ * ((1 - t) + t * x)⁻¹) t := by
      have ha : HasDerivAt (fun s : ℝ ↦ (1 - s) + s * x) (x - 1) t := by
        convert ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
          ((hasDerivAt_id t).mul_const x) using 1
        · funext s; dsimp
        · ring
      convert (hasDerivAt_id t).div ha (ne_of_gt (hp hx t ht)) using 1
      · rfl
      · dsimp; field_simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hc hx).mul (hc hx)).intervalIntegrable]
    simp [inverseLogMean]
  · have hf (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
        ((1 - t) + t * x)⁻¹ * ((1 - t) + t * y)⁻¹ =
          ((x - 1) * ((1 - t) + t * x)⁻¹ -
            (y - 1) * ((1 - t) + t * y)⁻¹) / (x - y) := by
      field_simp [ne_of_gt (hp hx t ht), ne_of_gt (hp hy t ht), sub_ne_zero.mpr hxy]
      ring
    rw [intervalIntegral.integral_congr hf, intervalIntegral.integral_div,
      intervalIntegral.integral_sub ((hc hx).const_mul _).intervalIntegrable
        ((hc hy).const_mul _).intervalIntegrable,
      integral_log_resolvent hx, integral_log_resolvent hy]
    simp [inverseLogMean, hxy]

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- The resolvent on a compact interval used to differentiate the matrix logarithm. -/
def logResolvent (σ : CMatrix a) (t : ℝ) : CMatrix a :=
  ((1 - t) • (1 : CMatrix a) + t • σ)⁻¹

theorem logResolvent_posDef {σ : CMatrix a} (hσ : σ.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - t) • (1 : CMatrix a) + t • σ).PosDef := by
  by_cases h : t = 1
  · simpa [h] using hσ
  · exact (Matrix.PosDef.one.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 h))).add_posSemidef
      (hσ.posSemidef.smul ht.1)

theorem logResolvent_continuousOn {σ : CMatrix a} (hσ : σ.PosDef) :
    ContinuousOn (logResolvent σ) (Set.Icc 0 1) := by
  intro t ht
  have hu := (logResolvent_posDef hσ ht).isUnit
  have hi : ContinuousAt Ring.inverse ((1 - t) • (1 : CMatrix a) + t • σ) := by
    simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
  have hc : Continuous (fun s : ℝ ↦ (1 - s) • (1 : CMatrix a) + s • σ) := by fun_prop
  change ContinuousWithinAt
    (fun s : ℝ ↦ ((1 - s) • (1 : CMatrix a) + s • σ)⁻¹) (Set.Icc 0 1) t
  simpa only [logResolvent, Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using
    (hi.comp (f := fun s : ℝ ↦ (1 - s) • (1 : CMatrix a) + s • σ)
      (hc.continuousAt (x := t))).continuousWithinAt

theorem logResolvent_spectral {σ : CMatrix a} (hσ : σ.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    logResolvent σ t = conjugation hσ.isHermitian.eigenvectorUnitary
      (Matrix.diagonal (fun i ↦
        (((1 - t) + t * hσ.isHermitian.eigenvalues i)⁻¹ : ℂ))) := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  have hc : (1 - t) • (1 : CMatrix a) + t • σ =
      conjugation U (Matrix.diagonal (fun i ↦ (((1 - t) + t * eig i : ℝ) : ℂ))) := by
    have hspec : σ = conjugation U (Matrix.diagonal (fun i ↦ (eig i : ℂ))) :=
      hσ.isHermitian.spectral_theorem
    rw [hspec]
    have h1 : conjugation U 1 = 1 := (conjStarAlgAut ℂ (CMatrix a) U).map_one
    conv_lhs => rw [← h1]
    rw [← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower, ← map_add]
    congr 1
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, hij, Complex.real_smul,
        Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  apply Matrix.inv_eq_left_inv
  change _ * ((1 - t) • (1 : CMatrix a) + t • σ) = 1
  rw [hc, ← conjugation_mul, Matrix.diagonal_mul_diagonal]
  have heq : Matrix.diagonal (fun i ↦
      ((((1 - t) + t * eig i)⁻¹ : ℂ) * (((1 - t) + t * eig i : ℝ) : ℂ))) =
      (1 : CMatrix a) := by
    ext i j
    by_cases h : i = j
    · subst j
      have hp := arithmetic_eigenvalue_pos (x := 1) (by norm_num)
        (hσ.eigenvalues_pos i) ht.1 ht.2
      simpa using (show (((1 - t) + t * eig i : ℝ) : ℂ)⁻¹ *
        (((1 - t) + t * eig i : ℝ) : ℂ) = 1 by
          rw [inv_mul_cancel₀]
          exact_mod_cast (ne_of_gt (by simpa using hp : 0 < (1 - t) + t * eig i)))
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  rw [heq]
  exact (conjStarAlgAut ℂ (CMatrix a) U).map_one

theorem log_eq_integral_resolvent {σ : CMatrix a} (hσ : σ.PosDef) :
    CFC.log σ = ∫ t : ℝ in 0..1, (σ - 1) * logResolvent σ t := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let f : ℝ → CMatrix a := fun t ↦ Matrix.diagonal (fun i ↦
    (((eig i - 1) * ((1 - t) + t * eig i)⁻¹ : ℝ) : ℂ))
  have hc : ContinuousOn f (Set.Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_matrix
    intro i j
    apply (continuousOn_iff_continuous_domRestrict
      (s := Set.Icc (0 : ℝ) 1) (f := fun t ↦ f t i j)).mp
    by_cases h : i = j
    · subst j
      have hi := continuousOn_arithmetic_inverse (x := 1) (by norm_num)
        (hσ.eigenvalues_pos i)
      simpa [f, eig, Function.comp_def] using
        Complex.continuous_ofReal.comp_continuousOn (hi.const_mul (eig i - 1))
    · simpa [f, Matrix.diagonal_apply, h] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (0 : ℂ)) (Set.Icc 0 1))
  have hfi : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hint : (∫ t : ℝ in 0..1, f t) =
      Matrix.diagonal (fun i ↦ (Real.log (eig i) : ℂ)) := by
    ext i j
    let evLin : CMatrix a →ₗ[ℂ] ℂ :=
      { toFun := fun Y ↦ Y i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have he := evLin.toContinuousLinearMap.intervalIntegral_comp_comm hfi
    change (∫ t : ℝ in 0..1, f t i j) = (∫ t : ℝ in 0..1, f t) i j at he
    rw [← he]
    by_cases h : i = j
    · subst j
      simp only [f, Matrix.diagonal_apply_eq, intervalIntegral.integral_ofReal]
      rw [integral_log_resolvent (hσ.eigenvalues_pos i)]
    · simp [f, Matrix.diagonal_apply, h]
  have hpoint (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      (σ - 1) * logResolvent σ t = conjugation U (f t) := by
    have hr := logResolvent_spectral hσ (by simpa using ht)
    have hspec : σ = conjugation U (Matrix.diagonal (fun i ↦ (eig i : ℂ))) :=
      hσ.isHermitian.spectral_theorem
    have h1 : conjugation U 1 = 1 := (conjStarAlgAut ℂ (CMatrix a) U).map_one
    rw [hr]
    change (σ - 1) * conjugation U
      (Matrix.diagonal (fun i ↦ (((1 - t) + t * eig i)⁻¹ : ℂ))) = _
    conv_lhs => lhs; rw [hspec, ← h1, ← map_sub]
    rw [← conjugation_mul]
    congr 1
    ext i j
    by_cases h : i = j <;>
      simp [f, Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply, h,
        Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv]
  rw [intervalIntegral.integral_congr hpoint]
  have hi := (conjugation U).toContinuousLinearMap.intervalIntegral_comp_comm hfi
  change (∫ t : ℝ in 0..1, conjugation U (f t)) = conjugation U (∫ t : ℝ in 0..1, f t) at hi
  rw [hi, hint, CFC.log, hσ.isHermitian.cfc_eq]
  rfl

/-- The derivative kernel is the inverse of the actual Kubo–Mori integral. -/
theorem inverseKuboMori_eq_integral_resolvent {σ : CMatrix a} (hσ : σ.PosDef)
    (X : CMatrix a) :
    inverseKuboMori hσ X =
      ∫ t : ℝ in 0..1, logResolvent σ t * X * logResolvent σ t := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let Z := conjugation (star U) X
  let f : ℝ → CMatrix a := fun t ↦ multiplier (fun ij ↦
    ((1 - t) + t * eig ij.1)⁻¹ * ((1 - t) + t * eig ij.2)⁻¹) Z
  have hc : ContinuousOn f (Set.Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_matrix
    intro i j
    apply (continuousOn_iff_continuous_domRestrict
      (s := Set.Icc (0 : ℝ) 1) (f := fun t ↦ f t i j)).mp
    change ContinuousOn (fun t : ℝ ↦
      ((((1 - t) + t * eig i)⁻¹ * ((1 - t) + t * eig j)⁻¹ : ℝ) : ℂ) * Z i j) _
    have hi := continuousOn_arithmetic_inverse (x := 1) (by norm_num) (hσ.eigenvalues_pos i)
    have hj := continuousOn_arithmetic_inverse (x := 1) (by norm_num) (hσ.eigenvalues_pos j)
    simpa using (Complex.continuous_ofReal.comp_continuousOn (hi.mul hj)).mul_const (Z i j)
  have hfi : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hint : (∫ t : ℝ in 0..1, f t) =
      multiplier (fun ij ↦ inverseLogMean (eig ij.1) (eig ij.2)) Z := by
    ext i j
    let evLin : CMatrix a →ₗ[ℂ] ℂ :=
      { toFun := fun Y ↦ Y i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have he := evLin.toContinuousLinearMap.intervalIntegral_comp_comm hfi
    change (∫ t : ℝ in 0..1, f t i j) = (∫ t : ℝ in 0..1, f t) i j at he
    rw [← he]
    change (∫ t : ℝ in 0..1,
      ((((1 - t) + t * eig i)⁻¹ * ((1 - t) + t * eig j)⁻¹ : ℝ) : ℂ) * Z i j) =
      (inverseLogMean (eig i) (eig j) : ℂ) * Z i j
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      integral_resolvent_product (hσ.eigenvalues_pos i) (hσ.eigenvalues_pos j)]
  have hpoint (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      logResolvent σ t * X * logResolvent σ t = conjugation U (f t) := by
    have hX : conjugation U Z = X := by
      simpa only [star_star] using conjugation_inverse (star U) X
    rw [logResolvent_spectral hσ (by simpa using ht), ← hX,
      ← conjugation_mul, ← conjugation_mul]
    congr 1
    ext i j
    simp [f, eig, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_mul,
      Complex.ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [intervalIntegral.integral_congr hpoint]
  have hi := (conjugation U).toContinuousLinearMap.intervalIntegral_comp_comm hfi
  change (∫ t : ℝ in 0..1, conjugation U (f t)) = conjugation U (∫ t : ℝ in 0..1, f t) at hi
  rw [hi, hint]
  rfl

end QuanIncapacity.BKM
