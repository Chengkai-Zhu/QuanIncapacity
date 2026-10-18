import QIT.Channels.Diamond
import QIT.Core.Map.ChoiCharacterization

/-!
# Matrix spaces and reference amplification

The Hilbert–Schmidt space uses the row-first identification
`|i⟩⟨j| ↔ |i,j⟩`, matching the manuscript's outer defect. All constructions
are for arbitrary finite systems, independently of the qutrit example.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT

namespace QuanIncapacity.MatrixSpace

variable {a b e r : Type*}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype e] [DecidableEq e] [Fintype r] [DecidableEq r]

def vec (X : CMatrix a) : a × a → ℂ := fun ij ↦ X ij.1 ij.2

def unvec (x : a × a → ℂ) : CMatrix a := fun i j ↦ x (i, j)

omit [Fintype a] [DecidableEq a] in
@[simp] theorem unvec_vec (X : CMatrix a) : unvec (vec X) = X := rfl
omit [Fintype a] [DecidableEq a] in
@[simp] theorem vec_unvec (x : a × a → ℂ) : vec (unvec x) = x := rfl

/-- Matrix of a superoperator in the orthonormal matrix-unit basis. -/
def rep (Φ : MatrixMap a b) : Matrix (b × b) (a × a) ℂ :=
  fun ij kl ↦ Φ (Matrix.single kl.1 kl.2 1) ij.1 ij.2

theorem rep_mulVec (Φ : MatrixMap a b) (X : CMatrix a) :
    rep Φ *ᵥ vec X = vec (Φ X) := by
  ext ij
  have h := congrFun (congrFun (MatrixMap.map_eq_sum_single Φ X) ij.1) ij.2
  simpa [rep, vec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using h.symm

omit [DecidableEq a] in
theorem trace_adjoint_mul (X Y : CMatrix a) :
    (X.conjTranspose * Y).trace = star (vec X) ⬝ᵥ vec Y := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    dotProduct, Fintype.sum_prod_type, vec, Pi.star_apply]
  exact Finset.sum_comm

/-- Hilbert–Schmidt adjoint, defined by the conjugate transpose of `rep Φ`. -/
def hsAdjoint (Φ : MatrixMap a b) : MatrixMap b a where
  toFun Y := unvec ((rep Φ).conjTranspose *ᵥ vec Y)
  map_add' X Y := by
    ext i j
    simp [unvec, vec, Matrix.mulVec, dotProduct, Finset.sum_add_distrib, mul_add]
  map_smul' c Y := by
    ext i j
    simp [unvec, vec, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

theorem hsAdjoint_pairing (Φ : MatrixMap a b) (X : CMatrix a) (Y : CMatrix b) :
    ((Φ X).conjTranspose * Y).trace = (X.conjTranspose * hsAdjoint Φ Y).trace := by
  rw [trace_adjoint_mul, trace_adjoint_mul, ← rep_mulVec]
  simp only [hsAdjoint, LinearMap.coe_mk, AddHom.coe_mk, vec_unvec,
    Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- Left multiplication as an operator on Hilbert–Schmidt space. -/
def left (X : CMatrix a) : CMatrix (a × a) := Matrix.kronecker X 1

theorem left_add (X Y : CMatrix a) : left (X + Y) = left X + left Y := by
  ext i j
  simp [left, Matrix.kronecker, add_mul]

theorem left_smul (c : ℂ) (X : CMatrix a) : left (c • X) = c • left X := by
  ext i j
  simp [left, Matrix.kronecker, mul_assoc]

theorem left_mulVec (X Y : CMatrix a) : left X *ᵥ vec Y = vec (X * Y) := by
  ext ij
  simp [left, vec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.one_apply, Matrix.mul_apply]

theorem left_quadratic (X Y : CMatrix a) :
    star (vec Y) ⬝ᵥ (left X *ᵥ vec Y) = (Y.conjTranspose * X * Y).trace := by
  rw [left_mulVec, ← trace_adjoint_mul, Matrix.mul_assoc]

/-- Reference amplification; references are always placed first. -/
def amp (r : Type*) [Fintype r] [DecidableEq r] (Φ : MatrixMap a b) :
    MatrixMap (r × a) (r × b) := MatrixMap.kron (Channel.idChannel r).map Φ

@[simp] theorem amp_apply (Φ : MatrixMap a b) (X : CMatrix (r × a))
    (i j : r × b) :
    amp r Φ X i j = Φ (fun k l ↦ X (i.1, k) (j.1, l)) i.2 j.2 :=
  MatrixMap.kron_idChannel_left_apply_slice Φ X i j

theorem amp_completelyPositive (Φ : MatrixMap a b)
    (hΦ : MatrixMap.IsCompletelyPositive Φ) : MatrixMap.IsCompletelyPositive (amp r Φ) :=
  MatrixMap.isCompletelyPositive_kron _ _ (Channel.idChannel r).completelyPositive hΦ

theorem rep_amp (Φ : MatrixMap a b) (i j : r) (k l : r) (x y : b) (z w : a) :
    rep (amp r Φ) ((i, x), (j, y)) ((k, z), (l, w)) =
      if k = i ∧ l = j then rep Φ (x, y) (z, w) else 0 := by
  unfold rep
  rw [amp_apply]
  by_cases hk : k = i <;> by_cases hl : l = j
  · subst k; subst l
    have hs : (fun p q ↦ Matrix.single (i, z) (j, w) (1 : ℂ) (i, p) (j, q)) =
        Matrix.single z w 1 := by ext p q; simp [Matrix.single]
    simp [hs]
  · have hs : (fun p q ↦ Matrix.single (k, z) (l, w) (1 : ℂ) (i, p) (j, q)) =
        (0 : CMatrix a) := by ext p q; simp [Matrix.single, hl]
    rw [hs, map_zero]
    simp [hl]
  · have hs : (fun p q ↦ Matrix.single (k, z) (l, w) (1 : ℂ) (i, p) (j, q)) =
        (0 : CMatrix a) := by ext p q; simp [Matrix.single, hk]
    rw [hs, map_zero]
    simp [hk]
  · have hs : (fun p q ↦ Matrix.single (k, z) (l, w) (1 : ℂ) (i, p) (j, q)) =
        (0 : CMatrix a) := by ext p q; simp [Matrix.single, hk]
    rw [hs, map_zero]
    simp [hk]

theorem amp_map_adjoint (Φ : MatrixMap a b)
    (hΦ : ∀ X, Φ X.conjTranspose = (Φ X).conjTranspose) (X : CMatrix (r × a)) :
    amp r Φ X.conjTranspose = (amp r Φ X).conjTranspose := by
  ext i j
  rw [amp_apply, Matrix.conjTranspose_apply, amp_apply]
  have hs : (fun k l ↦ X.conjTranspose (i.1, k) (j.1, l)) =
      Matrix.conjTranspose (fun k l ↦ X (j.1, k) (i.1, l)) := by ext k l; rfl
  rw [hs]
  exact congrFun (congrFun (hΦ (fun k l ↦ X (j.1, k) (i.1, l))) i.2) j.2

end QuanIncapacity.MatrixSpace
