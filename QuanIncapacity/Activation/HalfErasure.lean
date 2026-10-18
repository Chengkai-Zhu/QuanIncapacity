import QuanIncapacity.Activation.DephasedErasureChannel
import QuanIncapacity.Activation.PartnerStability

/-! The half-erasure channel and its full, identical complement, obtained
from one symmetric Stinespring isometry. -/

noncomputable section
open QIT
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.HalfErasure

variable {a : Type} [Fintype a] [DecidableEq a]

def matrix : Matrix (Option a × Option a) a ℂ := Matrix.of fun p i ↦
  match p with
  | (some j, none) => if j = i then (Real.sqrt 2 : ℂ)⁻¹ else 0
  | (none, some j) => if j = i then (Real.sqrt 2 : ℂ)⁻¹ else 0
  | _ => 0

theorem matrix_isometry : (matrix (a := a)).conjTranspose * matrix = (1 : CMatrix a) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fintype.sum_option, matrix, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    norm_num [Matrix.one_apply, ite_mul, mul_ite, sqrt_two_inv_mul_self]
  · simp [Matrix.one_apply, hij, Ne.symm hij, ite_mul, mul_ite]

def dilation : ReferenceIsometry a (Option a × Option a) :=
  ⟨matrix, matrix_isometry⟩

def channel : Channel a (Option a) := dilation.outputChannel

theorem matrix_swap (b e : Option a) (i : a) : matrix (b, e) i = matrix (e, b) i := by
  cases b <;> cases e <;> rfl

theorem lift_swap (X : CMatrix a) (b e b' e' : Option a) :
    ((dilation (a := a)).matrix * X * (dilation (a := a)).matrix.conjTranspose) (b, e) (b', e') =
      ((dilation (a := a)).matrix * X * (dilation (a := a)).matrix.conjTranspose) (e, b) (e', b') := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (dilation (a := a)).matrix (b', e') j = (dilation (a := a)).matrix (e', b') j from matrix_swap _ _ _]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (dilation (a := a)).matrix (b, e) i = (dilation (a := a)).matrix (e, b) i from matrix_swap _ _ _]

theorem complement_eq : (dilation (a := a)).complementaryChannel = channel := by
  apply channel_eq_of_map_eq
  ext X i j
  change dilation.complementaryChannel.map X i j = dilation.outputChannel.map X i j
  rw [ReferenceIsometry.complementaryChannel_map, ReferenceIsometry.outputChannel_map]
  unfold partialTraceA partialTraceB
  apply Finset.sum_congr rfl
  intro k _
  exact lift_swap X k i k j

theorem complementary : ComplementaryChannels (channel (a := a)) channel :=
  ⟨dilation, rfl, complement_eq⟩

theorem antidegradable : ∃ D : Channel (Option a) (Option a),
    D.map.comp (channel (a := a)).map = channel.map := by
  refine ⟨Channel.idChannel _, ?_⟩
  rw [idChannel_map_eq, LinearMap.id_comp]

theorem complete_order : CompleteRelativeEntropyOrder (channel (a := a)) channel :=
  completeRelativeEntropyOrder_of_antidegradable antidegradable

theorem channel_apply (X : CMatrix a) :
    (channel (a := a)).map X = DephasedErasure.matrix (1 / 2) 1 X := by
  change dilation.outputChannel.map X = _
  rw [ReferenceIsometry.outputChannel_map]
  ext b b'
  change partialTraceB ((matrix (a := a)) * X * (matrix (a := a)).conjTranspose) b b' = _
  simp only [partialTraceB, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_option, matrix, Matrix.of_apply]
  cases b <;> cases b' <;>
    simp [DephasedErasure.matrix, Matrix.trace, ite_mul, mul_ite, Finset.sum_mul,
      Finset.mul_sum, apply_ite, map_inv₀, Complex.conj_ofReal, ← mul_assoc, sqrt_two_inv_mul_self]
  all_goals ring_nf
  all_goals simp [sqrt_two_inv_sq, mul_comm]

theorem channel_eq : channel (a := a) =
    DephasedErasure.channel (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num) le_rfl := by
  apply channel_eq_of_map_eq
  rw [DephasedErasure.channel_map]
  exact LinearMap.ext channel_apply

end QuanIncapacity.HalfErasure
