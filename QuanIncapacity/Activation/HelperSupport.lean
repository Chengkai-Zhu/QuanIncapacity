import QuanIncapacity.Activation.HelperOutputs
import QuanIncapacity.Framework.ChoiGram
import QuanIncapacity.Framework.SupportProjector

/-! The actual support projector of the helper Choi state annihilates the
key `Z` sandwich, deduced from its full complementary output. -/

noncomputable section
open QIT
open scoped Matrix BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.Helper

def inputZ : CMatrix Q4 := (Matrix.diagonal ![1, -1]).kronecker (1 : CMatrix Qubit)

theorem inputZ_difference : inputZ = (2 : ℂ) • ((input 0).matrix - (input 1).matrix) := by
  rw [input_matrix, input_matrix]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [inputZ, Matrix.kronecker, Matrix.diagonal, Matrix.one_apply,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply]

theorem inputZ_transpose : inputZ.transpose = inputZ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [inputZ, Matrix.transpose_apply, Matrix.kronecker, Matrix.diagonal,
      Matrix.one_apply]

theorem environment_Z_zero : complement.map inputZ = 0 := by
  have h : complement.map (input 1).matrix = complement.map (input 0).matrix :=
    congrArg State.matrix (environment_output_equal 1)
  rw [inputZ_difference, map_smul, map_sub, h, sub_self, smul_zero]

def keyZ : CMatrix (Q4 × Q4) := inputZ.kronecker (1 : CMatrix Q4)

theorem kraus_Z_gram_zero : (ChoiGram.columns kraus).conjTranspose * keyZ *
    ChoiGram.columns kraus = 0 := by
  rw [keyZ, ChoiGram.gram_complement kraus kraus_tracePreserving, inputZ_transpose]
  change (complement.map inputZ).transpose = 0
  rw [environment_Z_zero, Matrix.transpose_zero]

def density : CMatrix (Q4 × Q4) := regrouped OmegaH

theorem density_positive : density.PosSemidef :=
  Omega_posSemidef.submatrix (fun p : Q4 × Q4 ↦ ((p.1.1, p.2.1), (p.1.2, p.2.2)))

theorem density_gram : density = (1 / 4 : ℂ) •
    (ChoiGram.columns kraus * (ChoiGram.columns kraus).conjTranspose) := by
  have h : (4 : ℝ) • density = ChoiGram.columns kraus * (ChoiGram.columns kraus).conjTranspose := by
    rw [← ChoiGram.choi_eq, ← channel_map_eq, M_H_choi]
    rfl
  ext p q
  have he := congrFun (congrFun h p) q
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul] at he ⊢
  norm_num at he ⊢
  linear_combination (1 / 4 : ℂ) * he

theorem density_Z_density_zero : density * keyZ * density = 0 := by
  rw [density_gram]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h : (ChoiGram.columns kraus * (ChoiGram.columns kraus).conjTranspose) * keyZ *
      (ChoiGram.columns kraus * (ChoiGram.columns kraus).conjTranspose) = 0 := by
    calc
      _ = ChoiGram.columns kraus * ((ChoiGram.columns kraus).conjTranspose * keyZ *
          ChoiGram.columns kraus) * (ChoiGram.columns kraus).conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [kraus_Z_gram_zero, Matrix.mul_zero, Matrix.zero_mul]
  rw [h, smul_zero]

def support : CMatrix (Q4 × Q4) := supportProjector density density_positive

/-- `Π_H (Z_A ⊗ I_{A'BB'}) Π_H = 0` for the actual normalized helper state,
in the input-first `AA':BB'` tensor order. -/
theorem support_orthogonality : support * keyZ * support = 0 :=
  supportProjector_sandwich_zero density density_positive keyZ density_Z_density_zero

end QuanIncapacity.Helper
