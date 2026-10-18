import QuanIncapacity.Framework.Shadowing
import QIT.States.MaximallyMixed

/-! Additional exact identities from the manuscript: operator sectors,
trace orthogonality of the defect Kraus operators, and the concrete signed
estimator variance example. -/

noncomputable section
open QIT
open scoped BigOperators Matrix

namespace QuanIncapacity

set_option backward.isDefEq.respectTransparency false

def scalarSector (X : CMatrix (Fin 3)) : CMatrix (Fin 3) :=
  (X.trace / 3) • 1

def symmetricSector (X : CMatrix (Fin 3)) : CMatrix (Fin 3) :=
  (1 / 2 : ℂ) • (X + X.transpose) - scalarSector X

def skewSector (X : CMatrix (Fin 3)) : CMatrix (Fin 3) :=
  (1 / 2 : ℂ) • (X - X.transpose)

theorem operator_sector_decomposition (X : CMatrix (Fin 3)) :
    X = scalarSector X + symmetricSector X + skewSector X := by
  ext i j
  simp only [scalarSector, symmetricSector, skewSector, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem lambda_sector_action (X : CMatrix (Fin 3)) :
    Λ_map X = scalarSector X + (1 / 4 : ℂ) • symmetricSector X +
      (3 / 4 : ℂ) • skewSector X := by
  ext i j
  simp only [Λ_map, scalarSector, symmetricSector, skewSector, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul]
  ring

theorem G_trace_orthogonal (μ ν : Fin 3) :
    ((G μ).conjTranspose * G ν).trace = if μ = ν then 4 else 0 := by
  fin_cases μ <;> fin_cases ν <;>
    norm_num [G, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, map_ofNat]

theorem maximallyMixed_qutrit_matrix :
    (State.maximallyMixed (Fin 3)).matrix = (1 / 3 : ℂ) • (1 : CMatrix (Fin 3)) := by
  rw [State.maximallyMixed_matrix]
  norm_num

theorem qutrit_example_shadow :
    𝒥_map (Matrix.single (0 : Fin 3) 0 1) =
      Matrix.diagonal ![(1 / 3 : ℂ), -1 / 3, 2 / 3, 2 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shadowEntries, Matrix.single, Matrix.trace, Matrix.diagonal,
      fin4ToFin3, avec, Matrix.mul_apply, Matrix.transpose_apply, A, levN]

theorem qutrit_example_receiver_variance :
    Var (Λ.applyState (State.maximallyMixed (Fin 3))).matrix
      (Matrix.single (0 : Fin 3) 0 1) = 2 / 9 := by
  change Var (Λ_map (State.maximallyMixed (Fin 3)).matrix) _ = _
  rw [maximallyMixed_qutrit_matrix, map_smul, Λ_one]
  norm_num [Var, Matrix.trace, Matrix.mul_apply, Matrix.single, Matrix.smul_apply]

theorem qutrit_example_environment_variance :
    Var (Λc.applyState (State.maximallyMixed (Fin 3))).matrix
      (𝒥_map (Matrix.single (0 : Fin 3) 0 1)) = 1 / 9 := by
  change Var (Λc_map (State.maximallyMixed (Fin 3)).matrix) _ = _
  rw [maximallyMixed_qutrit_matrix, map_smul, Λc_one, qutrit_example_shadow]
  norm_num [Var, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]

end QuanIncapacity
