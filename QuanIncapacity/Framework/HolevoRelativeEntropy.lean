import QuanIncapacity.Framework.RelativeEntropyRegularization
import QIT.Information.Entropy.Holevo

/-! Holevo information as average relative entropy, with singular average
states and zero-probability signals included. -/

noncomputable section
open QIT
open scoped ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

namespace QuanIncapacity

variable {a ι : Type*} [Fintype a] [DecidableEq a] [Fintype ι]

theorem vonNeumann_eq_neg_trace_mul_log (ρ : State a) :
    ρ.vonNeumann = -(ρ.matrix * CFC.log ρ.matrix).trace.re / Real.log 2 := by
  let U := ρ.pos.isHermitian.eigenvectorUnitary
  let eig := ρ.pos.isHermitian.eigenvalues
  have hs : ρ.matrix = MatrixSpace.conjugation U (Matrix.diagonal (fun i ↦ (eig i : ℂ))) :=
    ρ.pos.isHermitian.spectral_theorem
  have hl : CFC.log ρ.matrix = MatrixSpace.conjugation U
      (Matrix.diagonal (fun i ↦ (Real.log (eig i) : ℂ))) := by
    simpa only [one_smul, zero_smul, add_zero, one_mul] using
      BKM.log_affine_identity_spectral ρ.pos.isHermitian 1 0
  have ht : (ρ.matrix * CFC.log ρ.matrix).trace.re = ∑ i, eig i * Real.log (eig i) := by
    rw [hl, BKM.trace_mul_conjugation_diagonal, hs, MatrixSpace.conjugation_inverse]
    simp
  have hx (x : ℝ) : xlog2 x = x * Real.log x / Real.log 2 := by
    unfold xlog2 log2
    by_cases h : x = 0
    · simp [h]
    · simp [h]; ring
  rw [ht]
  simp only [State.vonNeumann, hx, ← Finset.sum_div]
  exact neg_div _ _ |>.symm

theorem supports_ensemble_average_of_pos (E : Ensemble ι a) (i : ι)
    (hi : 0 < (E.probs i : ℝ)) :
    Matrix.Supports (E.states i).matrix E.averageState.matrix := by
  classical
  let R : CMatrix a := ∑ j ∈ Finset.univ.erase i, (E.probs j : ℝ) • (E.states j).matrix
  have hR : R.PosSemidef := by
    exact Matrix.posSemidef_sum _ (fun j _ ↦ (E.states j).pos.smul (E.prob_nonneg j))
  have ha : E.averageState.matrix = R + (E.probs i : ℝ) • (E.states i).matrix := by
    change (∑ j, (E.probs j : ℝ) • (E.states j).matrix) = _
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  rw [ha]
  exact Matrix.Supports.of_pos_smul_right_add (E.states i).pos hR hi

/-- A zero-weight term contributes zero even if its relative entropy is infinite. -/
theorem weighted_relativeEntropy_ensemble (E : Ensemble ι a) (i : ι) :
    ((E.probs i : ℝ) : EReal) * (E.states i).relativeEntropy E.averageState =
      (((E.probs i : ℝ) * (-(E.states i).vonNeumann -
        ((E.states i).matrix * CFC.log E.averageState.matrix).trace.re / Real.log 2) : ℝ) : EReal) := by
  by_cases hi : (E.probs i : ℝ) = 0
  · simp [hi]
  · rw [BKM.relativeEntropy_eq_trace_of_supports _ _
      (supports_ensemble_average_of_pos E i (lt_of_le_of_ne (E.prob_nonneg i) (Ne.symm hi)))]
    exact (EReal.coe_mul _ _).symm

/-- The equality is in `EReal`: no finiteness of a zero-weight signal is assumed. -/
theorem holevoInformation_eq_sum_relativeEntropy (E : Ensemble ι a) :
    (E.holevoInformation : EReal) =
      ∑ i, ((E.probs i : ℝ) : EReal) * (E.states i).relativeEntropy E.averageState := by
  simp_rw [weighted_relativeEntropy_ensemble]
  have hc (f : ι → ℝ) : ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) :=
    map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f Finset.univ
  rw [← hc]
  congr 1
  have ht : (E.averageState.matrix * CFC.log E.averageState.matrix).trace.re =
      ∑ i, (E.probs i : ℝ) * ((E.states i).matrix * CFC.log E.averageState.matrix).trace.re := by
    rw [Ensemble.averageState_matrix, Matrix.sum_mul, Matrix.trace_sum]
    simp [Matrix.trace_smul, NNReal.smul_def, Complex.real_smul]
  rw [Ensemble.holevoInformation_def, vonNeumann_eq_neg_trace_mul_log E.averageState, ht]
  simp only [mul_sub, mul_neg, ← mul_div_assoc, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.sum_div]
  ring

end QuanIncapacity
