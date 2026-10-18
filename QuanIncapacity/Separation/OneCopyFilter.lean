import QuanIncapacity.Separation.ChoiDistillation
import QIT.Entanglement.PPT

/-! Actual local success filters on one Choi copy. They succeed with
probability `1/2` and produce a normalized entangled two-qubit state. -/

noncomputable section
open QIT
open scoped Matrix BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.OneCopyFilter

def filter : Matrix (Fin 2) (Fin 3) ℂ :=
  Matrix.of fun i j ↦ if j = i.castSucc then 1 else 0

def map : MatrixMap (Fin 3) (Fin 2) := MatrixMap.ofKraus (fun _ : Unit ↦ filter)

theorem map_apply (X : CMatrix (Fin 3)) :
    map X = X.submatrix (Fin.castSucc : Fin 2 → Fin 3) Fin.castSucc := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [map, filter, MatrixMap.ofKraus, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.submatrix_apply]

theorem map_legal : MatrixMap.TraceNonincreasingCP map where
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  traceNonincreasing := by
    intro X hX
    have hn : 0 ≤ (X (2 : Fin 3) 2).re := (Complex.nonneg_iff.mp hX.diag_nonneg).1
    rw [map_apply]
    simp [Matrix.trace, Matrix.submatrix_apply, Fin.sum_univ_succ, Complex.add_re]
    linarith

def jointFilter : Matrix (Fin 2 × Fin 2) Sys33 ℂ := filter.kronecker filter

def branch : CMatrix (Fin 2 × Fin 2) := jointFilter * omega * jointFilter.conjTranspose

theorem branch_submatrix : branch = omega.submatrix
    (fun p : Fin 2 × Fin 2 ↦ (p.1.castSucc, p.2.castSucc))
    (fun p : Fin 2 × Fin 2 ↦ (p.1.castSucc, p.2.castSucc)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [branch, jointFilter, filter, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.kronecker, Matrix.submatrix_apply]

theorem branch_positive : branch.PosSemidef :=
  omega_posSemidef.mul_mul_conjTranspose_same jointFilter

theorem joint_map_apply (X : CMatrix Sys33) : MatrixMap.kron map map X = X.submatrix
    (fun p : Fin 2 × Fin 2 ↦ (p.1.castSucc, p.2.castSucc))
    (fun p : Fin 2 × Fin 2 ↦ (p.1.castSucc, p.2.castSucc)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [MatrixMap.kron, map_apply, Matrix.submatrix_apply, Matrix.single_apply]

theorem actual_success_branch : MatrixMap.kron map map qutritChoiState.matrix = branch := by
  rw [joint_map_apply, branch_submatrix]
  rfl

theorem branch_trace : branch.trace = (1 / 2 : ℂ) := by
  rw [branch_submatrix]
  norm_num [Matrix.trace, Fintype.sum_prod_type, Matrix.submatrix_apply,
    omega, Pminus, Phi3, swap3, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]

def output : State (Fin 2 × Fin 2) where
  matrix := (2 : ℝ) • branch
  pos := branch_positive.smul (by norm_num : (0 : ℝ) ≤ 2)
  trace_eq_one := by rw [Matrix.trace_smul, branch_trace]; norm_num

theorem success_equation : branch = (1 / 2 : ℝ) • output.matrix := by
  change branch = (1 / 2 : ℝ) • ((2 : ℝ) • branch)
  rw [smul_smul]
  norm_num

def witness : Fin 2 × Fin 2 → ℂ := fun p ↦
  if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0

theorem negative_expectation : star witness ⬝ᵥ
    (partialTransposeB output.matrix *ᵥ witness) = (-1 / 3 : ℂ) := by
  simp only [output, branch_submatrix]
  norm_num [witness, partialTransposeB, Matrix.submatrix_apply, dotProduct,
    Matrix.mulVec, Fintype.sum_prod_type, omega, Pminus, Phi3, swap3,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]

theorem output_entangled : ¬ IsSeparable output := by
  intro hs
  have hp := isPPT_of_isSeparable hs
  have hn := (Complex.nonneg_iff.mp
    (hp.dotProduct_mulVec_nonneg witness)).1
  rw [negative_expectation] at hn
  norm_num at hn

/-- A local trace-nonincreasing CP success map on each party, positive
success probability, and an actual entangled qubit pair from one input copy. -/
theorem one_copy_entangled_branch : MatrixMap.TraceNonincreasingCP map ∧
    (0 : ℝ) < 1 / 2 ∧ branch = (1 / 2 : ℝ) • output.matrix ∧ ¬ IsSeparable output :=
  ⟨map_legal, by norm_num, success_equation, output_entangled⟩

end QuanIncapacity.OneCopyFilter
