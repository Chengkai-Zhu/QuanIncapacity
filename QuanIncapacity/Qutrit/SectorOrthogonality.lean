import QuanIncapacity.Qutrit.SectorDimensions

/-! Hilbert--Schmidt orthogonality of the actual three operator sectors. -/
noncomputable section
open QIT QuanIncapacity
open scoped Matrix

namespace QuanIncapacity.SectorDimensions

private theorem symmetric_skew_trace {X Y : CMatrix (Fin 3)}
    (hX : X.transpose = X) (hY : Y.transpose = -Y) : (X.conjTranspose * Y).trace = 0 := by
  have ht : X.conjTranspose.transpose = X.conjTranspose := by
    rw [← Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, hX]
  have he := Matrix.trace_transpose_mul X.conjTranspose Y
  rw [ht, hY, Matrix.mul_neg, Matrix.trace_neg] at he
  linear_combination (-1 / 2 : ℂ) * he

private theorem skew_trace {Y : CMatrix (Fin 3)} (hY : Y.transpose = -Y) : Y.trace = 0 := by
  have he := Matrix.trace_transpose Y
  rw [hY, Matrix.trace_neg] at he
  linear_combination (-1 / 2 : ℂ) * he

theorem orthogonal (X Y : CMatrix (Fin 3)) :
    ((scalarSector X).conjTranspose * symmetricSector Y).trace = 0 ∧
    ((scalarSector X).conjTranspose * skewSector Y).trace = 0 ∧
    ((symmetricSector X).conjTranspose * skewSector Y).trace = 0 := by
  have hS : (symmetricSector Y).transpose = symmetricSector Y ∧
      (symmetricSector Y).trace = 0 :=
    (symmetric_membership _).mp ⟨Y, projection_one Y⟩
  have hT : (skewSector Y).transpose = -skewSector Y :=
    (skew_membership _).mp ⟨Y, projection_two Y⟩
  have hSX : (symmetricSector X).transpose = symmetricSector X :=
    ((symmetric_membership _).mp ⟨X, projection_one X⟩).1
  refine ⟨?_, ?_, symmetric_skew_trace hSX hT⟩ <;>
    simp [scalarSector, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul,
      hS.2, skew_trace hT]

end QuanIncapacity.SectorDimensions
