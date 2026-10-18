import QuanIncapacity.Qutrit.Adjoint

/-! Standalone Levi-Civita, skew-vector and complementary-block formulas
from the supplemental manuscript, for arbitrary complex matrix arguments. -/

noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace QuanIncapacity

theorem levi_civita_contraction (j k l m : Fin 3) :
    ∑ μ : Fin 3, levN μ.val j.val k.val * levN μ.val l.val m.val =
      (if j = l then (1 : ℂ) else 0) * (if k = m then 1 else 0) -
        (if j = m then 1 else 0) * (if k = l then 1 else 0) := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases m <;>
    norm_num [levN, Fin.sum_univ_succ]

theorem skew_vector_sum (Y : CMatrix (Fin 3)) :
    ∑ μ : Fin 3, avec Y μ • A μ = Y - Y.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [avec, A, levN, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply]
  all_goals ring

def complementBlock (X : CMatrix (Fin 3)) : CMatrix (Fin 4) := Matrix.of fun i j ↦
  if hi : i = 0 then
    if hj : j = 0 then X.trace / 2
    else ((Real.sqrt 2 : ℂ)⁻¹ / 2) * avec X (fin4ToFin3 hj)
  else if hj : j = 0 then -((Real.sqrt 2 : ℂ)⁻¹ / 2) * avec X (fin4ToFin3 hi)
  else (1 / 4 : ℂ) * (X.trace * (if fin4ToFin3 hi = fin4ToFin3 hj then 1 else 0) -
    X (fin4ToFin3 hj) (fin4ToFin3 hi))

set_option maxHeartbeats 800000 in
theorem complement_block (X : CMatrix (Fin 3)) : Λc_map X = complementBlock X := by
  ext i j
  change (K i * X * (K j).conjTranspose).trace = complementBlock X i j
  fin_cases i <;> fin_cases j <;>
    simp [complementBlock, K, A, levN, avec, fin4ToFin3,
      Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      sqrt_two_inv_eq_half_sqrt]
  all_goals change Fin 3 → Fin 3 → ℂ at X
  all_goals norm_num [map_ofNat]
  all_goals ring_nf
  all_goals simp only [sqrt_two_sq]
  all_goals ring

def complementAdjointEntries (Z : CMatrix (Fin 4)) : CMatrix (Fin 3) := Matrix.of fun i j ↦
  (Z 0 0 / 2) * (if i = j then 1 else 0) +
    ((Real.sqrt 2 : ℂ)⁻¹ / 2) * ∑ μ : Fin 3,
      (Z 0 (fin3ToFin4 μ) - Z (fin3ToFin4 μ) 0) * A μ i j +
    (1 / 4 : ℂ) * ((∑ μ : Fin 3, Z (fin3ToFin4 μ) (fin3ToFin4 μ)) *
      (if i = j then 1 else 0) - Z (fin3ToFin4 j) (fin3ToFin4 i))

set_option maxHeartbeats 800000 in
theorem complement_adjoint_block (Z : CMatrix (Fin 4)) :
    MatrixMap.krausAdjoint Ec Z = complementAdjointEntries Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixMap.krausAdjoint, complementAdjointEntries, Ec, K, A, levN,
      fin3ToFin4, fin4ToFin3, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply, sqrt_two_inv_eq_half_sqrt]
  all_goals change Fin 4 → Fin 4 → ℂ at Z
  all_goals norm_num [map_ofNat]
  all_goals ring_nf
  all_goals simp only [sqrt_two_sq]
  all_goals ring

end QuanIncapacity
