import QuanIncapacity.Framework.HalfLineIntegral
import QuanIncapacity.Framework.LogResolvent
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! The paper's half-infinite Bochner resolvent formula for inverse
Kubo--Mori weights, for arbitrary complex perturbations and repeated spectra. -/

noncomputable section
open QIT MeasureTheory Unitary QuanIncapacity.MatrixSpace
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.BKM

variable {a : Type*} [Fintype a] [DecidableEq a]

def halfLineResolvent (σ : CMatrix a) (s : ℝ) : CMatrix a :=
  (σ + s • (1 : CMatrix a))⁻¹

theorem halfLineResolvent_spectral {σ : CMatrix a} (hσ : σ.PosDef)
    {s : ℝ} (hs : 0 ≤ s) :
    halfLineResolvent σ s = conjugation hσ.isHermitian.eigenvectorUnitary
      (Matrix.diagonal (fun i ↦ (((s + hσ.isHermitian.eigenvalues i)⁻¹ : ℝ) : ℂ))) := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  have hc : σ + s • (1 : CMatrix a) =
      conjugation U (Matrix.diagonal (fun i ↦ ((s + eig i : ℝ) : ℂ))) := by
    have hspec : σ = conjugation U (Matrix.diagonal (fun i ↦ (eig i : ℂ))) :=
      hσ.isHermitian.spectral_theorem
    have h1 : conjugation U 1 = 1 := (conjStarAlgAut ℂ (CMatrix a) U).map_one
    rw [hspec]
    conv_lhs => rhs; rw [← h1]
    rw [← LinearMap.map_smul_of_tower, ← map_add]
    congr 1
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, hij, Complex.real_smul,
        Complex.ofReal_add, add_comm]
  apply Matrix.inv_eq_left_inv
  change _ * (σ + s • (1 : CMatrix a)) = 1
  rw [hc, ← conjugation_mul, Matrix.diagonal_mul_diagonal]
  have heq : Matrix.diagonal (fun i ↦ ((((s + eig i)⁻¹ : ℝ) : ℂ) * ((s + eig i : ℝ) : ℂ))) =
      (1 : CMatrix a) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hp : 0 < s + eig i := add_pos_of_nonneg_of_pos hs (hσ.eigenvalues_pos i)
      simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using
        (show (((s + eig i)⁻¹ : ℝ) : ℂ) * ((s + eig i : ℝ) : ℂ) = 1 by
          rw [Complex.ofReal_inv]
          exact inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hp))
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  rw [heq]
  exact (conjStarAlgAut ℂ (CMatrix a) U).map_one

theorem inverseKuboMori_eq_integral_halfLine {σ : CMatrix a} (hσ : σ.PosDef)
    (X : CMatrix a) :
    inverseKuboMori hσ X =
      ∫ s : ℝ in Set.Ioi 0, halfLineResolvent σ s * X * halfLineResolvent σ s := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let Z := conjugation (star U) X
  let f : ℝ → CMatrix a := fun s ↦ multiplier
    (fun ij ↦ (s + eig ij.1)⁻¹ * (s + eig ij.2)⁻¹) Z
  have hfi : IntegrableOn f (Set.Ioi 0) := by
    apply integrable_pi_iff.mpr
    intro i
    apply integrable_pi_iff.mpr
    intro j
    exact ((halfLine_resolvent_integrable (hσ.eigenvalues_pos i)
      (hσ.eigenvalues_pos j)).ofReal).mul_const (Z i j)
  have hint : (∫ s : ℝ in Set.Ioi 0, f s) =
      multiplier (fun ij ↦ inverseLogMean (eig ij.1) (eig ij.2)) Z := by
    ext i j
    let evLin : CMatrix a →ₗ[ℂ] ℂ :=
      { toFun := fun Y ↦ Y i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have he := evLin.toContinuousLinearMap.integral_comp_comm hfi
    change (∫ s : ℝ in Set.Ioi 0, f s i j) = (∫ s : ℝ in Set.Ioi 0, f s) i j at he
    rw [← he]
    change (∫ s : ℝ in Set.Ioi 0, (((s + eig i)⁻¹ * (s + eig j)⁻¹ : ℝ) : ℂ) * Z i j) =
      (inverseLogMean (eig i) (eig j) : ℂ) * Z i j
    rw [integral_mul_const]
    have hc : (∫ s : ℝ in Set.Ioi 0, (((s + eig i)⁻¹ * (s + eig j)⁻¹ : ℝ) : ℂ)) =
        (inverseLogMean (eig i) (eig j) : ℂ) := by
      calc
        _ = ((∫ s : ℝ in Set.Ioi 0, (s + eig i)⁻¹ * (s + eig j)⁻¹ : ℝ) : ℂ) :=
          integral_complex_ofReal
        _ = _ := congrArg Complex.ofReal
          (integral_halfLine_resolvent (hσ.eigenvalues_pos i) (hσ.eigenvalues_pos j))
    exact congrArg (fun z : ℂ ↦ z * Z i j) hc
  have hpoint (s : ℝ) (hs : s ∈ Set.Ioi 0) :
      halfLineResolvent σ s * X * halfLineResolvent σ s = conjugation U (f s) := by
    have hs0 : 0 ≤ s := le_of_lt hs
    have hX : conjugation U Z = X := by
      simpa only [star_star] using conjugation_inverse (star U) X
    rw [halfLineResolvent_spectral hσ hs0, ← hX, ← conjugation_mul, ← conjugation_mul]
    congr 1
    ext i j
    simp [f, eig, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_mul,
      Complex.ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  have hi := (conjugation U).toContinuousLinearMap.integral_comp_comm hfi
  change (∫ s : ℝ in Set.Ioi 0, conjugation U (f s)) =
    conjugation U (∫ s : ℝ in Set.Ioi 0, f s) at hi
  rw [hi, hint]
  rfl

theorem halfLine_kernel_integrable {σ : CMatrix a} (hσ : σ.PosDef)
    (X : CMatrix a) : IntegrableOn
      (fun s : ℝ ↦ halfLineResolvent σ s * X * halfLineResolvent σ s) (Set.Ioi 0) := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let Z := conjugation (star U) X
  let f : ℝ → CMatrix a := fun s ↦ multiplier
    (fun ij ↦ (s + eig ij.1)⁻¹ * (s + eig ij.2)⁻¹) Z
  have hfi : IntegrableOn f (Set.Ioi 0) := by
    apply integrable_pi_iff.mpr
    intro i
    apply integrable_pi_iff.mpr
    intro j
    exact ((halfLine_resolvent_integrable (hσ.eigenvalues_pos i)
      (hσ.eigenvalues_pos j)).ofReal).mul_const (Z i j)
  have hpoint (s : ℝ) (hs : s ∈ Set.Ioi 0) :
      halfLineResolvent σ s * X * halfLineResolvent σ s = conjugation U (f s) := by
    have hX : conjugation U Z = X := by
      simpa only [star_star] using conjugation_inverse (star U) X
    rw [halfLineResolvent_spectral hσ (le_of_lt hs), ← hX,
      ← conjugation_mul, ← conjugation_mul]
    congr 1
    ext i j
    simp [f, eig, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_mul,
      Complex.ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
  exact ((conjugation U).toContinuousLinearMap.integrable_comp hfi).congr
    (ae_restrict_mem measurableSet_Ioi |>.mono fun s hs ↦ (hpoint s hs).symm)

/-- The scalar resolvent formula, with no commutativity or simple-spectrum assumption. -/
theorem metric_eq_integral_halfLine {σ : CMatrix a} (hσ : σ.PosDef) (X : CMatrix a) :
    metric hσ X = ∫ s : ℝ in Set.Ioi 0,
      (X.conjTranspose * halfLineResolvent σ s * X * halfLineResolvent σ s).trace.re := by
  let T : CMatrix a →ₗ[ℂ] ℂ :=
    { toFun := fun Z ↦ (X.conjTranspose * Z).trace
      map_add' := fun Z W ↦ by simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c Z ↦ by simp [Matrix.mul_smul, Matrix.trace_smul] }
  let L : CMatrix a →L[ℝ] ℝ :=
    Complex.reCLM.comp (T.toContinuousLinearMap.restrictScalars ℝ)
  have hi := L.integral_comp_comm (halfLine_kernel_integrable hσ X)
  change (∫ s : ℝ in Set.Ioi 0,
    (X.conjTranspose * (halfLineResolvent σ s * X * halfLineResolvent σ s)).trace.re) =
    (X.conjTranspose * (∫ s : ℝ in Set.Ioi 0,
      halfLineResolvent σ s * X * halfLineResolvent σ s)).trace.re at hi
  rw [← inverseKuboMori_eq_integral_halfLine hσ X] at hi
  simpa only [metric, Matrix.mul_assoc] using hi.symm

theorem metric_eq_integral_Ici {σ : CMatrix a} (hσ : σ.PosDef)
    (X : CMatrix a) (hX : X.IsHermitian) :
    metric hσ X = ∫ s : ℝ in Set.Ici 0,
      (X * (σ + s • (1 : CMatrix a))⁻¹ * X * (σ + s • (1 : CMatrix a))⁻¹).trace.re := by
  rw [integral_Ici_eq_integral_Ioi, metric_eq_integral_halfLine hσ X, hX.eq]
  rfl

theorem inverseKuboMori_eq_integral_Ici {σ : CMatrix a} (hσ : σ.PosDef)
    (X : CMatrix a) :
    inverseKuboMori hσ X =
      ∫ s : ℝ in Set.Ici 0, (σ + s • (1 : CMatrix a))⁻¹ * X *
        (σ + s • (1 : CMatrix a))⁻¹ := by
  rw [integral_Ici_eq_integral_Ioi]
  exact inverseKuboMori_eq_integral_halfLine hσ X

end QuanIncapacity.BKM
