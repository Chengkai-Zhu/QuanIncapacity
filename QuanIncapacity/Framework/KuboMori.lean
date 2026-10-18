import QuanIncapacity.Framework.SpectralMetric
import QuanIncapacity.Framework.ArithmeticCriterion

/-!
# Kubo–Mori weights and their inverse

The operators are constructed in an actual unitary eigenbasis using the
logarithmic mean. The geometric-integral identification is proved separately.
Repeated eigenvalues use the positive diagonal branch of the logarithmic mean.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT QuanIncapacity.MatrixSpace

namespace QuanIncapacity.BKM

variable {a b : Type*} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

def multiplier (f : a × a → ℝ) : MatrixMap a a where
  toFun X i j := (f (i, j) : ℂ) * X i j
  map_add' X Y := by
    ext i j
    change (f (i, j) : ℂ) * (X i j + Y i j) =
      (f (i, j) : ℂ) * X i j + (f (i, j) : ℂ) * Y i j
    ring
  map_smul' c X := by
    ext i j
    change (f (i, j) : ℂ) * (c * X i j) = c * ((f (i, j) : ℂ) * X i j)
    ring

@[simp] theorem multiplier_apply (f : a × a → ℝ) (X : CMatrix a) (i j : a) :
    multiplier f X i j = (f (i, j) : ℂ) * X i j := rfl

theorem multiplier_pairing (f : a × a → ℝ) (X : CMatrix a) :
    (X.conjTranspose * multiplier f X).trace.re =
      ∑ ij : a × a, f ij * Complex.normSq (X ij.1 ij.2) := by
  have hv : vec (multiplier f X) = Matrix.diagonal (fun ij ↦ (f ij : ℂ)) *ᵥ vec X := by
    ext ij
    simp [vec, Matrix.mulVec_diagonal]
  rw [trace_adjoint_mul, hv]
  exact quadratic_real_diagonal f (vec X)

def kuboMori {σ : CMatrix a} (hσ : σ.PosDef) : MatrixMap a a :=
  (conjugation hσ.isHermitian.eigenvectorUnitary).comp
    ((multiplier (fun ij ↦ logMean (hσ.isHermitian.eigenvalues ij.1)
      (hσ.isHermitian.eigenvalues ij.2))).comp
        (conjugation (star hσ.isHermitian.eigenvectorUnitary)))

def inverseKuboMori {σ : CMatrix a} (hσ : σ.PosDef) : MatrixMap a a :=
  (conjugation hσ.isHermitian.eigenvectorUnitary).comp
    ((multiplier (fun ij ↦ inverseLogMean (hσ.isHermitian.eigenvalues ij.1)
      (hσ.isHermitian.eigenvalues ij.2))).comp
        (conjugation (star hσ.isHermitian.eigenvectorUnitary)))

theorem inverseKuboMori_kuboMori {σ : CMatrix a} (hσ : σ.PosDef) (X : CMatrix a) :
    inverseKuboMori hσ (kuboMori hσ X) = X := by
  simp only [inverseKuboMori, kuboMori, LinearMap.comp_apply, conjugation_inverse]
  have hm :
      multiplier (fun ij ↦ inverseLogMean (hσ.isHermitian.eigenvalues ij.1)
        (hσ.isHermitian.eigenvalues ij.2))
        (multiplier (fun ij ↦ logMean (hσ.isHermitian.eigenvalues ij.1)
          (hσ.isHermitian.eigenvalues ij.2))
          (conjugation (star hσ.isHermitian.eigenvectorUnitary) X)) =
      conjugation (star hσ.isHermitian.eigenvectorUnitary) X := by
    ext i j
    have hp := ne_of_gt (inverseLogMean_pos (hσ.eigenvalues_pos i) (hσ.eigenvalues_pos j))
    simp [logMean, ← mul_assoc, hp]
  rw [hm]
  simpa only [star_star] using conjugation_inverse (star hσ.isHermitian.eigenvectorUnitary) X

theorem kuboMori_inverseKuboMori {σ : CMatrix a} (hσ : σ.PosDef) (X : CMatrix a) :
    kuboMori hσ (inverseKuboMori hσ X) = X := by
  simp only [inverseKuboMori, kuboMori, LinearMap.comp_apply, conjugation_inverse]
  have hm :
      multiplier (fun ij ↦ logMean (hσ.isHermitian.eigenvalues ij.1)
        (hσ.isHermitian.eigenvalues ij.2))
        (multiplier (fun ij ↦ inverseLogMean (hσ.isHermitian.eigenvalues ij.1)
          (hσ.isHermitian.eigenvalues ij.2))
          (conjugation (star hσ.isHermitian.eigenvectorUnitary) X)) =
      conjugation (star hσ.isHermitian.eigenvectorUnitary) X := by
    ext i j
    have hp := ne_of_gt (inverseLogMean_pos (hσ.eigenvalues_pos i) (hσ.eigenvalues_pos j))
    simp [logMean, ← mul_assoc, hp]
  rw [hm]
  simpa only [star_star] using conjugation_inverse (star hσ.isHermitian.eigenvectorUnitary) X

def metric {σ : CMatrix a} (hσ : σ.PosDef) (X : CMatrix a) : ℝ :=
  (X.conjTranspose * inverseKuboMori hσ X).trace.re

theorem metric_eq_arithmeticMetric {σ : CMatrix a} (hσ : σ.PosDef) (X : CMatrix a) :
    metric hσ X = arithmeticMetric σ X := by
  unfold metric
  rw [← conjugation_trace (star hσ.isHermitian.eigenvectorUnitary)
    (X.conjTranspose * inverseKuboMori hσ X), conjugation_mul, conjugation_adjoint]
  simp only [inverseKuboMori, LinearMap.comp_apply, conjugation_inverse]
  rw [multiplier_pairing, arithmeticMetric_spectral hσ]

theorem left_weight_to_bkm {σ : CMatrix a} {ω : CMatrix b}
    (hσ : σ.PosDef) (hω : ω.PosDef) (J : MatrixMap a b)
    (hJ : ∀ Y, J Y.conjTranspose = (J Y).conjTranspose)
    (h : ∀ Y, ((J Y).conjTranspose * ω * J Y).trace.re ≤
      (Y.conjTranspose * σ * Y).trace.re) (Z : CMatrix b) :
    metric hσ (hsAdjoint J Z) ≤ metric hω Z := by
  rw [metric_eq_arithmeticMetric, metric_eq_arithmeticMetric]
  exact arithmeticMetric_comparison hσ hω J hJ h Z

end QuanIncapacity.BKM
