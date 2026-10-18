import QuanIncapacity.Framework.LogDerivative
import QIT.Information.Entropy.RelativeEntropyTraceLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Relative entropy and its BKM Hessian

The trace formulas here use the actual CFC matrix logarithm. Natural-logarithm
trace entropy is kept distinct from Lean-QIT's relative entropy in bits.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology BigOperators
open QIT MeasureTheory QuanIncapacity.MatrixSpace

namespace QuanIncapacity.BKM

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem trace_mul_inverseKuboMori {σ : CMatrix a} (hσ : σ.PosDef) (X : CMatrix a) :
    (σ * inverseKuboMori hσ X).trace = X.trace := by
  let U := hσ.isHermitian.eigenvectorUnitary
  let eig := hσ.isHermitian.eigenvalues
  let Z := conjugation (star U) X
  have hspec : σ = conjugation U (Matrix.diagonal (fun i ↦ (eig i : ℂ))) :=
    hσ.isHermitian.spectral_theorem
  have hd := congrArg (conjugation (star U)) hspec
  rw [conjugation_inverse] at hd
  rw [← conjugation_trace (star U) (σ * inverseKuboMori hσ X), conjugation_mul, hd]
  simp only [inverseKuboMori, LinearMap.comp_apply]
  change (Matrix.diagonal (fun i ↦ (eig i : ℂ)) * conjugation (star U)
    (conjugation U (multiplier (fun ij ↦ inverseLogMean (eig ij.1) (eig ij.2)) Z))).trace = _
  rw [conjugation_inverse]
  rw [← conjugation_trace (star U) X]
  change _ = Z.trace
  simp only [Matrix.trace, Matrix.diagonal_mul, multiplier_apply, inverseLogMean, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (eig i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hσ.eigenvalues_pos i))
  simp [Complex.ofReal_inv, ← mul_assoc, hi]

def realTrace : CMatrix a →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap a ℝ ℂ).toContinuousLinearMap

@[simp] theorem realTrace_apply (X : CMatrix a) : realTrace X = X.trace.re := rfl

/-- The convex trace function whose Bregman divergence is relative entropy. -/
def traceEntropy (σ : CMatrix a) : ℝ := (σ * CFC.log σ).trace.re

theorem traceEntropy_hasDerivAt [Nonempty a] {σ X : CMatrix a} {u : ℝ}
    (hσ : (σ + u • X).PosDef) (hX : X.IsHermitian) :
    HasDerivAt (fun v : ℝ ↦ traceEntropy (σ + v • X))
      ((X * CFC.log (σ + u • X)).trace.re + X.trace.re) u := by
  have hσX : HasDerivAt (fun v : ℝ ↦ σ + v • X) X u := by
    simpa using ((hasDerivAt_id u).smul_const X).const_add σ
  have hp := hσX.mul (log_hasDerivAt_affine hσ hX)
  have ht := HasFDerivAt.comp_hasDerivAt (x := u) realTrace.hasFDerivAt hp
  simpa only [Function.comp_def, realTrace_apply, Matrix.trace_add, Complex.add_re,
    trace_mul_inverseKuboMori, traceEntropy, Pi.mul_apply] using ht

theorem traceEntropy_hasDerivAt_derivative [Nonempty a] {σ X : CMatrix a} {u : ℝ}
    (hσ : (σ + u • X).PosDef) (hX : X.IsHermitian) :
    HasDerivAt (fun v : ℝ ↦ (X * CFC.log (σ + v • X)).trace.re + X.trace.re)
      (metric hσ X) u := by
  have hp := (log_hasDerivAt_affine hσ hX).const_mul X
  have ht := (HasFDerivAt.comp_hasDerivAt (x := u) realTrace.hasFDerivAt hp).add_const X.trace.re
  simpa only [Function.comp_def, realTrace_apply, metric, hX.eq] using ht

/-- A non-normalized trace formula; state relative entropy divides it by `ln 2`. -/
def relativeEntropyNat (ρ σ : CMatrix a) : ℝ :=
  (ρ * (CFC.log ρ - CFC.log σ)).trace.re

theorem relativeEntropy_eq_nat_of_posDef (ρ σ : State a)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) :
    ρ.relativeEntropy σ = ((relativeEntropyNat ρ.matrix σ.matrix / Real.log 2 : ℝ) : EReal) := by
  rw [State.relativeEntropy_eq_coe_posDefFinite_of_posDef ρ σ hρ hσ]
  congr 1
  simp only [State.relativeEntropyPosDefFinite, State.psdLog, relativeEntropyNat,
    CFC.log, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, div_eq_mul_inv]

theorem relativeEntropyNat_hasDerivAt [Nonempty a] {σ X τ : CMatrix a} {u : ℝ}
    (hσ : (σ + u • X).PosDef) (hX : X.IsHermitian) :
    HasDerivAt (fun v : ℝ ↦ relativeEntropyNat (σ + v • X) τ)
      ((X * CFC.log (σ + u • X)).trace.re + X.trace.re -
        (X * CFC.log τ).trace.re) u := by
  have hσX : HasDerivAt (fun v : ℝ ↦ σ + v • X) X u := by
    simpa using ((hasDerivAt_id u).smul_const X).const_add σ
  have ht := HasFDerivAt.comp_hasDerivAt (x := u) realTrace.hasFDerivAt
    (hσX.mul_const (CFC.log τ))
  have hh := (traceEntropy_hasDerivAt hσ hX).sub ht
  simpa only [relativeEntropyNat, traceEntropy, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re, Function.comp_def, realTrace_apply, Pi.sub_def] using hh

theorem relativeEntropyNat_hasDerivAt_derivative [Nonempty a]
    {σ X τ : CMatrix a} {u : ℝ} (hσ : (σ + u • X).PosDef) (hX : X.IsHermitian) :
    HasDerivAt (fun v : ℝ ↦ (X * CFC.log (σ + v • X)).trace.re + X.trace.re -
        (X * CFC.log τ).trace.re) (metric hσ X) u :=
  (traceEntropy_hasDerivAt_derivative hσ hX).sub_const _

end QuanIncapacity.BKM
