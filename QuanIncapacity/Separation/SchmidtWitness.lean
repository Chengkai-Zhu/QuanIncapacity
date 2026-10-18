import QuanIncapacity.Separation.ChoiSpectrum
import QIT.States.Purification.Uhlmann

/-! The normalized negative-partial-transpose witness and its actual Schmidt
rank, defined by the rank of the bipartite coefficient matrix. -/

noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.SchmidtWitness

def amplitude (p : Sys33) : ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ * (if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0)

def vector : PureVector Sys33 where
  amp := amplitude
  trace_rankOne_eq_one := by
    norm_num [rankOneMatrix_trace, dotProduct, amplitude, Fintype.sum_prod_type,
      sqrt_two_inv_mul_self, ← mul_assoc]

def coefficient : CMatrix (Fin 3) := Matrix.of fun i j ↦ vector.amp (i, j)

def inclusion : Matrix (Fin 3) (Fin 2) ℂ :=
  Matrix.of fun i j ↦ if i = j.castSucc then 1 else 0

theorem coefficient_factor : coefficient = inclusion * coefficient.submatrix Fin.castSucc id := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coefficient, vector, amplitude, inclusion, Matrix.mul_apply,
      Matrix.submatrix_apply, Fin.sum_univ_two]

theorem coefficient_rank : coefficient.rank = 2 := by
  have hup : coefficient.rank ≤ 2 := by
    rw [coefficient_factor]
    exact (Matrix.rank_mul_le_left _ _).trans (by
      simpa using Matrix.rank_le_card_width inclusion)
  have hdet : (coefficient.submatrix (Fin.castSucc : Fin 2 → Fin 3) Fin.castSucc).det ≠ 0 := by
    norm_num [coefficient, vector, amplitude, Matrix.det_fin_two,
      Matrix.submatrix_apply, sqrt_two_inv_mul_self]
  have hlow := Matrix.rank_submatrix_le coefficient
    (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc : Fin 2 → Fin 3)
  rw [Matrix.rank_of_det_ne_zero hdet] at hlow
  norm_num at hlow
  exact le_antisymm hup hlow

theorem expectation : star vector.amp ⬝ᵥ (ptA omega *ᵥ vector.amp) = (-1 / 12 : ℂ) := by
  norm_num [vector, amplitude, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    ptA, omega, Pminus, Phi3, swap3, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.one_apply]
  ring_nf
  norm_num [sqrt_two_inv_sq]

theorem expectation_negative : (star vector.amp ⬝ᵥ
    (partialTransposeA qutritChoiState.matrix *ᵥ vector.amp)).re < 0 := by
  change (star vector.amp ⬝ᵥ (ptA omega *ᵥ vector.amp)).re < 0
  rw [expectation]
  norm_num

end QuanIncapacity.SchmidtWitness
