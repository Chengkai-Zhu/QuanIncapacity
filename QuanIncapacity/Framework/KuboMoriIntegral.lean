import QuanIncapacity.Framework.KuboMori
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The spectral operator is the manuscript's actual Bochner integral. -/

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators Matrix Matrix.Norms.L2Operator
open QIT MeasureTheory QuanIncapacity.MatrixSpace

namespace QuanIncapacity.BKM

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem kuboMori_eq_integral {σ : CMatrix a} (hσ : σ.PosDef) (X : CMatrix a) :
    kuboMori hσ X = ∫ s : ℝ in 0..1, CFC.rpow σ s * X * CFC.rpow σ (1 - s) := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let Z := conjugation (star U) X
  let f : ℝ → CMatrix a := fun s ↦
    multiplier (fun ij ↦ eig ij.1 ^ s * eig ij.2 ^ (1 - s)) Z
  have hX : conjugation U Z = X := by
    simpa only [star_star] using conjugation_inverse (star U) X
  have hpow (s : ℝ) : CFC.rpow σ s =
      conjugation U (Matrix.diagonal (fun i ↦ ((eig i ^ s : ℝ) : ℂ))) := by
    have hc : CFC.rpow σ s = cfc (fun x : ℝ ↦ x ^ s) σ :=
      CFC.rpow_eq_cfc_real hσ.posSemidef.nonneg
    rw [hc, hσ.isHermitian.cfc_eq]
    rfl
  have hf : Continuous f := by
    apply continuous_matrix
    intro i j
    change Continuous (fun s : ℝ ↦ ((eig i ^ s * eig j ^ (1 - s) : ℝ) : ℂ) * Z i j)
    have hi := Real.continuous_const_rpow (ne_of_gt (hσ.eigenvalues_pos i))
    have hj := Real.continuous_const_rpow (ne_of_gt (hσ.eigenvalues_pos j))
    exact (Complex.continuous_ofReal.comp
      (hi.mul (hj.comp (continuous_const.sub continuous_id)))).mul_const _
  have hfi : IntervalIntegrable f volume (0 : ℝ) 1 := hf.intervalIntegrable _ _
  have hfint : (∫ s : ℝ in 0..1, f s) =
      multiplier (fun ij ↦ logMean (eig ij.1) (eig ij.2)) Z := by
    ext i j
    let evLin : CMatrix a →ₗ[ℂ] ℂ :=
      { toFun := fun Y ↦ Y i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let ev : CMatrix a →L[ℂ] ℂ := evLin.toContinuousLinearMap
    have he := ev.intervalIntegral_comp_comm hfi
    change (∫ s : ℝ in 0..1, f s i j) = (∫ s : ℝ in 0..1, f s) i j at he
    rw [← he]
    change (∫ s : ℝ in 0..1, ((eig i ^ s * eig j ^ (1 - s) : ℝ) : ℂ) * Z i j) =
      (logMean (eig i) (eig j) : ℂ) * Z i j
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      integral_geometric (hσ.eigenvalues_pos i) (hσ.eigenvalues_pos j)]
  have hpoint (s : ℝ) : CFC.rpow σ s * X * CFC.rpow σ (1 - s) = conjugation U (f s) := by
    rw [hpow s, hpow (1 - s)]
    calc
      _ = conjugation U (Matrix.diagonal (fun i ↦ ((eig i ^ s : ℝ) : ℂ))) *
          conjugation U Z *
          conjugation U (Matrix.diagonal (fun i ↦ ((eig i ^ (1 - s) : ℝ) : ℂ))) := by rw [hX]
      _ = conjugation U (Matrix.diagonal (fun i ↦ ((eig i ^ s : ℝ) : ℂ)) * Z *
          Matrix.diagonal (fun i ↦ ((eig i ^ (1 - s) : ℝ) : ℂ))) := by
        rw [conjugation_mul, conjugation_mul]
      _ = _ := by
        apply congrArg (conjugation U)
        ext i j
        simp [f, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_mul,
          mul_assoc, mul_comm, mul_left_comm]
  simp_rw [hpoint]
  have hc := (conjugation U).toContinuousLinearMap.intervalIntegral_comp_comm hfi
  change (∫ s : ℝ in 0..1, conjugation U (f s)) = conjugation U (∫ s : ℝ in 0..1, f s) at hc
  rw [hc, hfint]
  rfl

end QuanIncapacity.BKM
