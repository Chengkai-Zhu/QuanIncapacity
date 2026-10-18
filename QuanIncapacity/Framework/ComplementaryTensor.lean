import QuanIncapacity.Framework.ChannelPair
import QuanIncapacity.Framework.TensorOrder

/-! A common Stinespring dilation for product channels, retaining both full
environments and fixing the tensor-factor order. -/

noncomputable section
open QIT
open scoped ComplexOrder MatrixOrder BigOperators Matrix

namespace QuanIncapacity

variable {a b c d e f g : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
variable [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
variable [Fintype g] [DecidableEq g]

namespace Stinespring

def reindexOutput (V : ReferenceIsometry a b) (v : b ≃ c) : ReferenceIsometry a c where
  matrix := V.matrix.submatrix v.symm id
  isometry := by
    ext i j
    change (∑ k : c, star (V.matrix (v.symm k) i) * V.matrix (v.symm k) j) = _
    exact (Equiv.sum_comp v.symm (fun k ↦ star (V.matrix k i) * V.matrix k j)).trans
      (congrFun (congrFun V.isometry i) j)

theorem reindexOutput_lift (V : ReferenceIsometry a b) (v : b ≃ c) (X : CMatrix a) :
    (reindexOutput V v).matrix * X * (reindexOutput V v).matrixᴴ =
      (V.matrix * X * V.matrixᴴ).submatrix v.symm v.symm := by
  ext i j
  rfl

def regroup (b e d f : Type) : (b × e) × (d × f) ≃ (b × d) × (e × f) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def product (V : ReferenceIsometry a (b × e)) (W : ReferenceIsometry c (d × f)) :
    ReferenceIsometry (a × c) ((b × d) × (e × f)) :=
  reindexOutput (V.prod W) (regroup b e d f)

theorem product_lift_kronecker (V : ReferenceIsometry a (b × e))
    (W : ReferenceIsometry c (d × f)) (X : CMatrix a) (Y : CMatrix c) :
    (product V W).matrix * X.kronecker Y * (product V W).matrixᴴ =
      ((V.matrix * X * V.matrixᴴ).kronecker (W.matrix * Y * W.matrixᴴ)).submatrix
        (regroup b e d f).symm (regroup b e d f).symm := by
  rw [product, reindexOutput_lift]
  congr 1
  change (V.matrix.kronecker W.matrix) * (X.kronecker Y) *
    (V.matrix.kronecker W.matrix)ᴴ = _
  rw [show (V.matrix.kronecker W.matrix)ᴴ = V.matrixᴴ.kronecker W.matrixᴴ from
    Matrix.conjTranspose_kronecker V.matrix W.matrix]
  rw [show V.matrix.kronecker W.matrix * X.kronecker Y =
    (V.matrix * X).kronecker (W.matrix * Y) from
    (Matrix.mul_kronecker_mul V.matrix X W.matrix Y).symm]
  exact (Matrix.mul_kronecker_mul (V.matrix * X) V.matrixᴴ
    (W.matrix * Y) W.matrixᴴ).symm

theorem output_product_kronecker (V : ReferenceIsometry a (b × e))
    (W : ReferenceIsometry c (d × f)) (X : CMatrix a) (Y : CMatrix c) :
    (product V W).outputChannel.map (X.kronecker Y) =
      (V.outputChannel.map X).kronecker (W.outputChannel.map Y) := by
  rw [ReferenceIsometry.outputChannel_map, product_lift_kronecker,
    ReferenceIsometry.outputChannel_map, ReferenceIsometry.outputChannel_map]
  ext i j
  simp [partialTraceB, Fintype.sum_prod_type, regroup, Matrix.kronecker,
    ← Finset.mul_sum, ← Finset.sum_mul]

theorem complement_product_kronecker (V : ReferenceIsometry a (b × e))
    (W : ReferenceIsometry c (d × f)) (X : CMatrix a) (Y : CMatrix c) :
    (product V W).complementaryChannel.map (X.kronecker Y) =
      (V.complementaryChannel.map X).kronecker (W.complementaryChannel.map Y) := by
  rw [ReferenceIsometry.complementaryChannel_map, product_lift_kronecker,
    ReferenceIsometry.complementaryChannel_map, ReferenceIsometry.complementaryChannel_map]
  ext i j
  simp [partialTraceA, Fintype.sum_prod_type, regroup, Matrix.kronecker,
    ← Finset.mul_sum, ← Finset.sum_mul]

end Stinespring

theorem matrixMap_eq_of_kronecker (Φ Ψ : MatrixMap (a × c) g)
    (h : ∀ X : CMatrix a, ∀ Y : CMatrix c, Φ (X.kronecker Y) = Ψ (X.kronecker Y)) : Φ = Ψ := by
  have hs : ∀ i j : a × c, Φ (Matrix.single i j 1) = Ψ (Matrix.single i j 1) := by
    intro i j
    rw [single_prod_eq_kronecker_single]
    exact h _ _
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single Φ X, MatrixMap.map_eq_sum_single Ψ X]
  simp only [hs]

theorem ComplementaryChannels.prod {N : Channel a b} {M : Channel a e}
    {P : Channel c d} {Q : Channel c f} (h : ComplementaryChannels N M)
    (h' : ComplementaryChannels P Q) : ComplementaryChannels (N.prod P) (M.prod Q) := by
  obtain ⟨V, rfl, rfl⟩ := h
  obtain ⟨W, rfl, rfl⟩ := h'
  refine ⟨Stinespring.product V W, ?_, ?_⟩
  · apply channel_eq_of_map_eq
    apply matrixMap_eq_of_kronecker
    intro X Y
    rw [Stinespring.output_product_kronecker]
    exact (MatrixMap.kron_apply_kronecker _ _ X Y).symm
  · apply channel_eq_of_map_eq
    apply matrixMap_eq_of_kronecker
    intro X Y
    rw [Stinespring.complement_product_kronecker]
    exact (MatrixMap.kron_apply_kronecker _ _ X Y).symm

theorem complementary_unit :
    ComplementaryChannels (Channel.unit : Channel PUnit.{1} PUnit.{1})
      (Channel.unit : Channel PUnit.{1} PUnit.{1}) := by
  let V : ReferenceIsometry PUnit.{1} (PUnit.{1} × PUnit.{1}) :=
    ReferenceIsometry.ofEquiv (Equiv.punitProd PUnit.{1}).symm
  refine ⟨V, ?_, ?_⟩ <;> apply channel_eq_of_map_eq <;> ext X i j
  · cases i; cases j
    have ht := V.outputChannel.tracePreserving X
    change V.outputChannel.map X PUnit.unit PUnit.unit = X PUnit.unit PUnit.unit
    simpa only [Matrix.trace, Matrix.diag_apply, Fintype.sum_unique] using ht
  · cases i; cases j
    have ht := V.complementaryChannel.tracePreserving X
    change V.complementaryChannel.map X PUnit.unit PUnit.unit = X PUnit.unit PUnit.unit
    simpa only [Matrix.trace, Matrix.diag_apply, Fintype.sum_unique] using ht

theorem ComplementaryChannels.tensorPower {N : Channel a b} {M : Channel a e}
    (h : ComplementaryChannels N M) :
    ∀ n : ℕ, ComplementaryChannels (N.tensorPower n) (M.tensorPower n)
  | 0 => complementary_unit
  | n + 1 => h.prod (h.tensorPower n)

end QuanIncapacity
