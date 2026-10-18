import QuanIncapacity.Framework.ChannelPair

/-! Input-first vectorized Kraus columns and their exact complementary-output
Gram matrix. The transpose on the input test matrix is explicit. -/

noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.ChoiGram

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

def columns (K : e → Matrix b a ℂ) : Matrix (a × b) e ℂ :=
  Matrix.of fun p l ↦ K l p.2 p.1

theorem choi_eq (K : e → Matrix b a ℂ) :
    MatrixMap.choi (MatrixMap.ofKraus K) = columns K * (columns K).conjTranspose := by
  rw [MatrixMap.choi_ofKraus]
  ext p q
  simp [columns, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec, Matrix.sum_apply]

theorem gram_test (K : e → Matrix b a ℂ) (H : CMatrix a) (l m : e) :
    ((columns K).conjTranspose * H.kronecker (1 : CMatrix b) * columns K) l m =
      (K m * H.transpose * (K l).conjTranspose).trace := by
  simp [columns, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace,
    Matrix.kronecker, Matrix.one_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, mul_ite, ite_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem gram_complement (K : e → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K)) (H : CMatrix a) :
    (columns K).conjTranspose * H.kronecker (1 : CMatrix b) * columns K =
      ((MatrixMap.krausStinespringIsometry K hTP).complementaryChannel.map H.transpose).transpose := by
  ext l m
  rw [gram_test, Matrix.transpose_apply, Stinespring.complementary_kraus_map]

end QuanIncapacity.ChoiGram
