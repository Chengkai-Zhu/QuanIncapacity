import QuanIncapacity.Separation.ChoiState

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators
open QIT
namespace QuanIncapacity

/-- The explicit matrix is the normalized Choi matrix of the actual channel. -/
lemma omega_eq_normalized_choi : omega = (1 / 3 : ℂ) • MatrixMap.choi Λ.map := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [omega, Phi3, Pminus, swap3, MatrixMap.choi, Λ, Λ_map,
      Matrix.trace, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]

lemma omega_posSemidef : omega.PosSemidef := by
  rw [omega_eq_normalized_choi]
  exact Λ.completelyPositive.smul (by
    apply Complex.nonneg_iff.mpr
    norm_num)

lemma omega_trace_one : omega.trace = 1 := by
  norm_num [omega, Phi3, Pminus, swap3, Matrix.trace, Fintype.sum_prod_type]

def qutritChoiState : State Sys33 where
  matrix := omega
  pos := omega_posSemidef
  trace_eq_one := omega_trace_one

/-- NPT of the normalized Choi matrix, with the channel connection made explicit. -/
theorem qutrit_choi_npt :
    ¬ (partialTransposeA ((1 / 3 : ℂ) • MatrixMap.choi Λ.map)).PosSemidef := by
  rw [← omega_eq_normalized_choi]
  exact omega_not_PPT

end QuanIncapacity
