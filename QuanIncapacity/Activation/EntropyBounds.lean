import QuanIncapacity.Framework.ComplementaryInformation

/-! Entropy foundations for the private-to-coherent conversion. These are
actual finite-state statements, with zero-weight branches allowed. -/

noncomputable section
open QIT
open scoped BigOperators

namespace QuanIncapacity.Activation

variable {r b ι : Type} [Fintype r] [DecidableEq r]
variable [Fintype b] [DecidableEq b] [Fintype ι] [DecidableEq ι]

/-- The entropy cost is for the binary component label, regardless of system dimension. -/
theorem coherentInformation_binaryMix_ge (p : ℝ) (ρ σ : State (r × b))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * ρ.coherentInformation + p * σ.coherentInformation - QIT.binaryEntropy p ≤
      (State.binaryMix p ρ σ hp0 hp1).coherentInformation := by
  have h := State.conditionalEntropy_binaryMix_le p ρ σ hp0 hp1
  simp only [State.coherentInformation]
  linarith

def receiverFlagEquiv (ι r b : Type) : ι × (r × b) ≃ r × (ι × b) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def receiverFlaggedState (E : Ensemble ι (r × b)) : State (r × (ι × b)) :=
  E.cqState.reindex (receiverFlagEquiv ι r b)

theorem receiverFlaggedState_marginalB (E : Ensemble ι (r × b)) :
    (receiverFlaggedState E).marginalB = E.marginalBipartiteB.cqState := by
  apply State.ext
  ext i j
  simp [receiverFlaggedState, receiverFlagEquiv, State.reindex,
    State.marginalB, Ensemble.cqState_matrix, Ensemble.marginalBipartiteB,
    Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.single_apply, partialTraceA, Finset.sum_comm]
  simp only [Finset.smul_sum]

/-- Orthogonal receiver flags average coherent information exactly. The
Shannon entropy of the branch flag cancels; no positive-weight premise is used. -/
theorem receiverFlaggedState_coherentInformation (E : Ensemble ι (r × b)) :
    (receiverFlaggedState E).coherentInformation =
      ∑ i, (E.probs i : ℝ) * (E.states i).coherentInformation := by
  rw [State.coherentInformation_eq, receiverFlaggedState_marginalB]
  unfold receiverFlaggedState
  rw [State.vonNeumann_reindex, State.cqState_vonNeumann, State.cqState_vonNeumann]
  simp only [Ensemble.marginalBipartiteB, State.coherentInformation_eq]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end QuanIncapacity.Activation
