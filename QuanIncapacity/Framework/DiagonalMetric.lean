import QuanIncapacity.Framework.ArithmeticMetric

noncomputable section
set_option maxHeartbeats 800000
open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT MeasureTheory

namespace QuanIncapacity.MatrixSpace

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem arithmetic_diagonal (eig : a → ℝ) (t : ℝ) :
    arithmetic (Matrix.diagonal (fun i ↦ (eig i : ℂ))) t =
      Matrix.diagonal (fun ij : a × a ↦ (((1 - t) * eig ij.1 + t * eig ij.2 : ℝ) : ℂ)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [arithmetic, left, right, Matrix.kronecker, Matrix.one_apply,
      Matrix.diagonal_apply, hik, hjl, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_sub]

theorem inverse_real_diagonal (f : a → ℝ) (hf : ∀ i, f i ≠ 0) :
    (Matrix.diagonal (fun i ↦ (f i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i ↦ ((f i)⁻¹ : ℂ)) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [hf i]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

theorem quadratic_real_diagonal (f : a → ℝ) (x : a → ℂ) :
    quadratic (Matrix.diagonal (fun i ↦ (f i : ℂ))) x =
      ∑ i, f i * Complex.normSq (x i) := by
  simp only [quadratic, Matrix.mulVec_diagonal, dotProduct, Complex.re_sum,
    Pi.star_apply, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem arithmeticMetric_diagonal (eig : a → ℝ) (heig : ∀ i, 0 < eig i) (Z : CMatrix a) :
    arithmeticMetric (Matrix.diagonal (fun i ↦ (eig i : ℂ))) Z =
      ∑ ij : a × a, BKM.inverseLogMean (eig ij.1) (eig ij.2) * Complex.normSq (Z ij.1 ij.2) := by
  unfold arithmeticMetric
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      quadratic (arithmetic (Matrix.diagonal (fun i ↦ (eig i : ℂ))) t)⁻¹ (vec Z) =
        ∑ ij : a × a, ((1 - t) * eig ij.1 + t * eig ij.2)⁻¹ *
          Complex.normSq (Z ij.1 ij.2) := by
    rw [arithmetic_diagonal]
    have hi := inverse_real_diagonal
      (fun ij : a × a ↦ (1 - t) * eig ij.1 + t * eig ij.2)
      (fun ij ↦ ne_of_gt (BKM.arithmetic_eigenvalue_pos (heig ij.1) (heig ij.2) ht.1 ht.2))
    rw [hi]
    simpa only [vec, Complex.ofReal_inv] using quadratic_real_diagonal
      (fun ij : a × a ↦ ((1 - t) * eig ij.1 + t * eig ij.2)⁻¹) (vec Z)
  have hint (ij : a × a) : IntervalIntegrable
      (fun t : ℝ ↦ ((1 - t) * eig ij.1 + t * eig ij.2)⁻¹ *
        Complex.normSq (Z ij.1 ij.2)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (BKM.continuousOn_arithmetic_inverse (heig ij.1) (heig ij.2)).mul_const _
  rw [intervalIntegral.integral_congr (fun t ht ↦ hp t (by simpa using ht))]
  rw [intervalIntegral.integral_finsetSum (fun ij _ ↦ hint ij)]
  apply Finset.sum_congr rfl
  intro ij _
  rw [intervalIntegral.integral_mul_const, BKM.integral_arithmetic_inverse (heig ij.1) (heig ij.2)]

end QuanIncapacity.MatrixSpace
