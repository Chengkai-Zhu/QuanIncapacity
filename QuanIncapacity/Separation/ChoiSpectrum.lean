import QuanIncapacity.Separation.ChoiBridge
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Exact diagonalization of the partial transpose, with every multiplicity.
The basis is rational and orthogonal, so no square-root normalization is
needed to identify the complete characteristic polynomial and rank. -/

noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.ChoiSpectrum

def pair (k : Fin 3) : Sys33 :=
  if k = 0 then (0, 1) else if k = 1 then (0, 2) else (1, 2)

def basisMatrix : CMatrix Sys33 := Matrix.of fun p q ↦
  if q.1 = 0 then
    if p.1 = p.2 then
      if q.2 = 0 then 1
      else if q.2 = 1 then (if p.1 = 0 then 1 else if p.1 = 1 then -1 else 0)
      else (if p.1 = 2 then -2 else 1)
    else 0
  else (if p = pair q.2 then 1 else 0) +
    (if p = (pair q.2).swap then (if q.1 = 1 then 1 else -1) else 0)

def normSquare (q : Sys33) : ℂ :=
  if q.1 = 0 then (if q.2 = 0 then 3 else if q.2 = 1 then 2 else 6) else 2

def inverseMatrix : CMatrix Sys33 := Matrix.of fun q p ↦ basisMatrix p q / normSquare q

set_option maxHeartbeats 1200000 in
theorem left_inverse : inverseMatrix * basisMatrix = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [inverseMatrix, basisMatrix, normSquare, pair, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.one_apply]

set_option maxHeartbeats 1200000 in
theorem right_inverse : basisMatrix * inverseMatrix = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [inverseMatrix, basisMatrix, normSquare, pair, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.one_apply]

def eigenvalue (q : Sys33) : ℂ :=
  if q = (0, 0) then 0 else if q.1 = 2 then -1 / 12 else 1 / 4

set_option maxHeartbeats 1200000 in
theorem diagonalization : ptA omega * basisMatrix = basisMatrix * Matrix.diagonal eigenvalue := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [ptA, omega, Pminus, Phi3, swap3, basisMatrix, pair, eigenvalue,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diagonal, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]

theorem similarity : ptA omega = basisMatrix * Matrix.diagonal eigenvalue * inverseMatrix := by
  rw [← diagonalization, Matrix.mul_assoc, right_inverse, Matrix.mul_one]

theorem charpoly_eq : (ptA omega).charpoly =
    (Polynomial.X - Polynomial.C (1 / 4 : ℂ)) ^ 5 * Polynomial.X *
      (Polynomial.X + Polynomial.C (1 / 12 : ℂ)) ^ 3 := by
  rw [similarity, Matrix.charpoly_mul_comm]
  rw [← Matrix.mul_assoc, left_inverse, Matrix.one_mul, Matrix.charpoly_diagonal]
  norm_num [Fintype.prod_prod_type, Fin.prod_univ_succ, eigenvalue]
  ring

theorem roots (z : ℂ) : Polynomial.IsRoot (ptA omega).charpoly z ↔
    z = (1 / 4 : ℂ) ∨ z = 0 ∨ z = (-1 / 12 : ℂ) := by
  simp only [charpoly_eq, Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    mul_eq_zero, pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0),
    pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0), sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; linear_combination h
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · right; rw [h]; norm_num

theorem rank : (ptA omega).rank = 8 := by
  classical
  have hd : (Matrix.diagonal eigenvalue).rank = 8 := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    rw [Finset.card_eq_sum_ones]
    simp only [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
    norm_num [eigenvalue]
  have hdiag : inverseMatrix * ptA omega * basisMatrix = Matrix.diagonal eigenvalue := by
    rw [Matrix.mul_assoc, diagonalization, ← Matrix.mul_assoc, left_inverse, Matrix.one_mul]
  have hlow := (Matrix.rank_mul_le_left (inverseMatrix * ptA omega) basisMatrix).trans
    (Matrix.rank_mul_le_right inverseMatrix (ptA omega))
  rw [hdiag, hd] at hlow
  have hup : (ptA omega).rank ≤ 8 := by
    rw [similarity]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans_eq hd
  exact le_antisymm hup hlow

def originalEigenvalue (q : Sys33) : ℂ :=
  if q = (0, 0) then 1 / 2 else if q.1 = 2 then 1 / 6 else 0

set_option maxHeartbeats 1200000 in
theorem original_diagonalization : omega * basisMatrix =
    basisMatrix * Matrix.diagonal originalEigenvalue := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [omega, Pminus, Phi3, swap3, basisMatrix, pair, originalEigenvalue,
      Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diagonal, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]

theorem original_similarity : omega =
    basisMatrix * Matrix.diagonal originalEigenvalue * inverseMatrix := by
  rw [← original_diagonalization, Matrix.mul_assoc, right_inverse, Matrix.mul_one]

theorem original_charpoly : omega.charpoly =
    Polynomial.X ^ 5 * (Polynomial.X - Polynomial.C (1 / 2 : ℂ)) *
      (Polynomial.X - Polynomial.C (1 / 6 : ℂ)) ^ 3 := by
  rw [original_similarity, Matrix.charpoly_mul_comm]
  rw [← Matrix.mul_assoc, left_inverse, Matrix.one_mul, Matrix.charpoly_diagonal]
  norm_num [Fintype.prod_prod_type, Fin.prod_univ_succ, originalEigenvalue]
  ring

theorem original_rank : omega.rank = 4 := by
  classical
  have hd : (Matrix.diagonal originalEigenvalue).rank = 4 := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_eq_sum_ones]
    simp only [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
    norm_num [originalEigenvalue]
  have hdiag : inverseMatrix * omega * basisMatrix = Matrix.diagonal originalEigenvalue := by
    rw [Matrix.mul_assoc, original_diagonalization, ← Matrix.mul_assoc, left_inverse, Matrix.one_mul]
  have hlo := (Matrix.rank_mul_le_left (inverseMatrix * omega) basisMatrix).trans
    (Matrix.rank_mul_le_right inverseMatrix omega)
  rw [hdiag, hd] at hlo
  have hhi : omega.rank ≤ 4 := by
    rw [original_similarity]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans_eq hd
  exact le_antisymm hhi hlo

end QuanIncapacity.ChoiSpectrum
