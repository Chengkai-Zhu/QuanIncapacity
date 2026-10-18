import QuanIncapacity.Qutrit.AlgebraicConsequences
import QuanIncapacity.Framework.MatrixSpace
import QuanIncapacity.Separation.ChoiSpectrum

/-! Dimensions of the scalar, symmetric-traceless and skew operator
sectors. The subspaces are actual ranges of their complex-linear projections. -/

noncomputable section
open QIT QuanIncapacity.MatrixSpace QuanIncapacity.ChoiSpectrum
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.SectorDimensions

def scalarMap : MatrixMap (Fin 3) (Fin 3) where
  toFun := scalarSector
  map_add' X Y := by
    ext i j
    simp [scalarSector, Matrix.trace_add, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, add_div, add_mul]
  map_smul' z X := by
    ext i j
    simp [scalarSector, Matrix.trace_smul, Matrix.smul_apply, smul_eq_mul]
    ring

def transposeMap : MatrixMap (Fin 3) (Fin 3) :=
  (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap

def projection (s : Fin 3) : MatrixMap (Fin 3) (Fin 3) :=
  if s = 0 then scalarMap
  else if s = 1 then (1 / 2 : ℂ) • (LinearMap.id + transposeMap) - scalarMap
  else (1 / 2 : ℂ) • (LinearMap.id - transposeMap)

theorem projection_zero (X : CMatrix (Fin 3)) : projection 0 X = scalarSector X := by
  simp [projection, scalarMap]

theorem projection_one (X : CMatrix (Fin 3)) : projection 1 X = symmetricSector X := by
  simp [projection, transposeMap, scalarMap, symmetricSector]

theorem projection_two (X : CMatrix (Fin 3)) : projection 2 X = skewSector X := by
  simp [projection, transposeMap, skewSector]

def selector (s : Fin 3) (q : Sys33) : ℂ :=
  if s = 0 then (if q = (0, 0) then 1 else 0)
  else if s = 1 then (if q ≠ (0, 0) ∧ q.1 ≠ 2 then 1 else 0)
  else (if q.1 = 2 then 1 else 0)

set_option maxHeartbeats 2400000 in
theorem diagonalization (s : Fin 3) :
    rep (projection s) * basisMatrix = basisMatrix * Matrix.diagonal (selector s) := by
  have hc (k : Fin 3) : (Finset.univ.filter (fun x : Fin 3 ↦ k = x)).card = 1 := by
    rw [show Finset.univ.filter (fun x : Fin 3 ↦ k = x) = {k} by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_comm]
    simp
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases s <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [rep, projection, scalarMap, scalarSector, transposeMap,
      Matrix.transposeLinearEquiv, Matrix.transposeAddEquiv, selector,
      basisMatrix, pair, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.trace,
      Matrix.single_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.diagonal, Matrix.one_apply]
  all_goals norm_num [hc]

theorem diagonal_rank (s : Fin 3) :
    (Matrix.diagonal (selector s)).rank = if s = 0 then 1 else if s = 1 then 5 else 3 := by
  classical
  rw [Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]
  fin_cases s <;> norm_num [selector]

theorem projection_rep_rank (s : Fin 3) :
    (rep (projection s)).rank = if s = 0 then 1 else if s = 1 then 5 else 3 := by
  have hdiag : inverseMatrix * rep (projection s) * basisMatrix = Matrix.diagonal (selector s) := by
    rw [Matrix.mul_assoc, diagonalization, ← Matrix.mul_assoc, left_inverse, Matrix.one_mul]
  have hsim : rep (projection s) = basisMatrix * Matrix.diagonal (selector s) * inverseMatrix := by
    rw [← diagonalization, Matrix.mul_assoc, right_inverse, Matrix.mul_one]
  have hlo := (Matrix.rank_mul_le_left (inverseMatrix * rep (projection s)) basisMatrix).trans
    (Matrix.rank_mul_le_right inverseMatrix (rep (projection s)))
  rw [hdiag, diagonal_rank] at hlo
  have hhi : (rep (projection s)).rank ≤ (Matrix.diagonal (selector s)).rank := by
    rw [hsim]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [diagonal_rank] at hhi
  exact le_antisymm hhi hlo

def vectorize : CMatrix (Fin 3) ≃ₗ[ℂ] (Sys33 → ℂ) where
  toFun := vec
  invFun := unvec
  left_inv := unvec_vec
  right_inv := vec_unvec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rep_rank_eq_range_finrank (Φ : MatrixMap (Fin 3) (Fin 3)) :
    (rep Φ).rank = Module.finrank ℂ (LinearMap.range Φ) := by
  have hmap : (rep Φ).mulVecLin = vectorize.toLinearMap.comp (Φ.comp vectorize.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    exact rep_mulVec Φ (unvec x)
  rw [Matrix.rank, hmap, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top Φ vectorize.symm.range]
  exact vectorize.finrank_map_eq _

theorem dimensions (s : Fin 3) : Module.finrank ℂ (LinearMap.range (projection s)) =
    if s = 0 then 1 else if s = 1 then 5 else 3 := by
  rw [← rep_rank_eq_range_finrank, projection_rep_rank]

theorem scalar_membership (Y : CMatrix (Fin 3)) : Y ∈ LinearMap.range (projection 0) ↔
    ∃ c : ℂ, Y = c • (1 : CMatrix (Fin 3)) := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X.trace / 3, projection_zero X⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c • (1 : CMatrix (Fin 3)), ?_⟩
    rw [projection_zero]
    simp [scalarSector, Matrix.trace_smul, smul_smul]

theorem symmetric_membership (Y : CMatrix (Fin 3)) : Y ∈ LinearMap.range (projection 1) ↔
    Y.transpose = Y ∧ Y.trace = 0 := by
  constructor
  · rintro ⟨X, rfl⟩
    rw [projection_one]
    constructor
    · ext i j
      simp [symmetricSector, scalarSector, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul,
        eq_comm (a := i) (b := j)]
      ring
    · simp [symmetricSector, scalarSector, Matrix.trace_sub, Matrix.trace_smul,
        Matrix.trace_add, Matrix.trace_transpose]
      ring
  · rintro ⟨hY, ht⟩
    refine ⟨Y, ?_⟩
    rw [projection_one]
    ext i j
    simp [symmetricSector, scalarSector, hY, ht, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, smul_eq_mul]
    ring

theorem skew_membership (Y : CMatrix (Fin 3)) : Y ∈ LinearMap.range (projection 2) ↔
    Y.transpose = -Y := by
  constructor
  · rintro ⟨X, rfl⟩
    rw [projection_two]
    ext i j
    simp [skewSector, Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.neg_apply, smul_eq_mul]
    ring
  · intro hY
    refine ⟨Y, ?_⟩
    rw [projection_two]
    ext i j
    simp [skewSector, hY, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
    ring

end QuanIncapacity.SectorDimensions
