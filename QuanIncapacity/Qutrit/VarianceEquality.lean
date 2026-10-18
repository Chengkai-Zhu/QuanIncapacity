import QuanIncapacity.Qutrit.AlgebraicConsequences
import QuanIncapacity.Framework.CompleteShadowing
import QIT.States.PosSqrt

/-! The residual-vector sum of squares and the exact faithful-input
variance equality condition from the manuscript. -/

noncomputable section
open QIT
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace QuanIncapacity

def residual (μ : Fin 3) (Y : CMatrix (Fin 3)) : Fin 3 → ℂ :=
  fun i ↦ Y i μ + (1 / 2 : ℂ) * Y μ i -
    (1 / 2 : ℂ) * Y.trace * (if i = μ then 1 else 0)

theorem residual_eq_adjoint (μ : Fin 3) (Y : CMatrix (Fin 3)) :
    residual μ Y = (G μ).conjTranspose *ᵥ flat Y := by
  ext i
  fin_cases μ <;> fin_cases i <;>
    norm_num [residual, G, flat, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.trace, map_ofNat]
  all_goals ring

theorem defect_quadratic_sos (ρ Y : CMatrix (Fin 3)) :
    star (flat Y) ⬝ᵥ (Δ_defect ρ *ᵥ flat Y) =
      ((2 / 9 : ℝ) : ℂ) * ∑ μ : Fin 3, star (residual μ Y) ⬝ᵥ (ρ *ᵥ residual μ Y) := by
  rw [Δ_defect_eq_Δ]
  change star (flat Y) ⬝ᵥ
    ((((2 / 9 : ℝ) : ℂ) • ∑ μ : Fin 3, G μ * ρ * (G μ).conjTranspose) *ᵥ flat Y) = _
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro μ _
  rw [residual_eq_adjoint]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    Shadowing.quadratic_pullback ρ (G μ).conjTranspose (flat Y)

theorem qutrit_variance_residuals (ρ Y : CMatrix (Fin 3)) (hY : Y.IsHermitian) :
    Var (Λ_map ρ) Y - Var (Λc_map ρ) (𝒥_map Y) =
      (2 / 9 : ℝ) * ∑ μ : Fin 3, (star (residual μ Y) ⬝ᵥ (ρ *ᵥ residual μ Y)).re := by
  have hJ : (𝒥_map Y).conjTranspose = 𝒥_map Y := by
    rw [← 𝒥_adjoint_preserving, hY.eq]
  have h := secondMoment_eq_defect ρ Y
  rw [defect_quadratic_sos, hY.eq, hJ,
    ← Matrix.trace_mul_cycle (Λ_map ρ) Y Y,
    ← Matrix.trace_mul_cycle (Λc_map ρ) (𝒥_map Y) (𝒥_map Y)] at h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.re_sum] at hr
  unfold Var
  rw [mean_agree]
  linarith

theorem sqrt_quadratic_normSq (ρ : State (Fin 3)) (x : Fin 3 → ℂ) :
    (star x ⬝ᵥ (ρ.matrix *ᵥ x)).re =
      ∑ i : Fin 3, Complex.normSq ((ρ.sqrtMatrix *ᵥ x) i) := by
  have h := Shadowing.quadratic_pullback (1 : CMatrix (Fin 3)) ρ.sqrtMatrix x
  rw [ρ.sqrtMatrix_isHermitian.eq, Matrix.mul_one, ρ.sqrtMatrix_mul_self,
    Matrix.one_mulVec] at h
  rw [h]
  have hn (z : ℂ) : (star z * z).re = Complex.normSq z := by
    simp [Complex.normSq, Complex.star_def, Complex.mul_re]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, hn]

/-- The norms are explicitly Euclidean squared norms, not the sup norm
of a function-space instance. -/
theorem qutrit_variance_sum_normSq (ρ : State (Fin 3)) (Y : CMatrix (Fin 3))
    (hY : Y.IsHermitian) :
    Var (Λ.applyState ρ).matrix Y - Var (Λc.applyState ρ).matrix (𝒥_map Y) =
      (2 / 9 : ℝ) * ∑ μ : Fin 3, ∑ i : Fin 3,
        Complex.normSq ((ρ.sqrtMatrix *ᵥ residual μ Y) i) := by
  change Var (Λ_map ρ.matrix) Y - Var (Λc_map ρ.matrix) (𝒥_map Y) = _
  rw [qutrit_variance_residuals ρ.matrix Y hY]
  simp only [sqrt_quadratic_normSq]

theorem residuals_zero_iff_scalar (Y : CMatrix (Fin 3)) :
    (∀ μ : Fin 3, residual μ Y = 0) ↔ Y = (Y.trace / 3) • (1 : CMatrix (Fin 3)) := by
  constructor
  · intro h
    ext i j
    have hi := congrFun (h j) i
    have hj := congrFun (h i) j
    change Y i j + (1 / 2 : ℂ) * Y j i -
      (1 / 2 : ℂ) * Y.trace * (if i = j then 1 else 0) = 0 at hi
    change Y j i + (1 / 2 : ℂ) * Y i j -
      (1 / 2 : ℂ) * Y.trace * (if j = i then 1 else 0) = 0 at hj
    have hd : (if j = i then (1 : ℂ) else 0) = (if i = j then 1 else 0) := by
      simp only [eq_comm]
    rw [hd] at hj
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    linear_combination (4 / 3 : ℂ) * hi - (2 / 3 : ℂ) * hj
  · intro h μ
    ext i
    have he := congrFun (congrFun h i) μ
    have he' := congrFun (congrFun h μ) i
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at he he'
    change Y i μ + (1 / 2 : ℂ) * Y μ i -
      (1 / 2 : ℂ) * Y.trace * (if i = μ then 1 else 0) = 0
    rw [he, he']
    simp only [eq_comm]
    ring

theorem qutrit_variance_eq_iff_scalar (ρ : State (Fin 3)) (hρ : ρ.matrix.PosDef)
    (Y : CMatrix (Fin 3)) (hY : Y.IsHermitian) :
    Var (Λ.applyState ρ).matrix Y = Var (Λc.applyState ρ).matrix (𝒥_map Y) ↔
      Y = (Y.trace / 3) • (1 : CMatrix (Fin 3)) := by
  rw [← residuals_zero_iff_scalar]
  have hs := qutrit_variance_residuals ρ.matrix Y hY
  have hn (μ : Fin 3) : 0 ≤ (star (residual μ Y) ⬝ᵥ (ρ.matrix *ᵥ residual μ Y)).re :=
    (Complex.nonneg_iff.mp (hρ.posSemidef.dotProduct_mulVec_nonneg _)).1
  constructor
  · intro heq
    have hz : ∑ μ : Fin 3, (star (residual μ Y) ⬝ᵥ (ρ.matrix *ᵥ residual μ Y)).re = 0 := by
      change Var (Λ_map ρ.matrix) Y = Var (Λc_map ρ.matrix) (𝒥_map Y) at heq
      rw [heq, sub_self] at hs
      linarith
    intro μ
    have hμ := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ ↦ hn μ)).mp hz μ (Finset.mem_univ μ)
    by_contra hr
    have hp := (Complex.pos_iff.mp (hρ.dotProduct_mulVec_pos hr)).1
    linarith
  · intro hz
    simp only [hz, star_zero, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re,
      Finset.sum_const_zero, mul_zero] at hs
    exact sub_eq_zero.mp hs

end QuanIncapacity
