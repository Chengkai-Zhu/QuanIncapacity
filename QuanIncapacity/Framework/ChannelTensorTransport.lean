import QuanIncapacity.Framework.ChannelSimulation
import QIT.Coding.Classical.HSWDirect.TensorPower

/-! Physical padding and tensor permutations for finite channel blocks. -/

noncomputable section
open QIT
open scoped BigOperators Matrix

namespace QuanIncapacity

set_option backward.isDefEq.respectTransparency false

variable {a b c d : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
variable [Fintype d] [DecidableEq d]

theorem channel_eq_of_single (N M : Channel a b)
    (h : ∀ i j, N.map (Matrix.single i j 1) = M.map (Matrix.single i j 1)) : N = M := by
  apply channel_eq_of_map_eq
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single N.map X, MatrixMap.map_eq_sum_single M.map X]
  simp only [h]

theorem channel_reindex_map (v : a ≃ b) (X : CMatrix a) :
    (Channel.reindex v).map X = X.submatrix v.symm v.symm := by
  change MatrixMap.ofReferenceIsometry (ReferenceIsometry.ofEquiv v) X = _
  rw [MatrixMap.ofReferenceIsometry_apply]
  ext i j
  change (∑ y, (∑ x, (if i = v x then (1 : ℂ) else 0) * X x y) *
    star (if j = v y then (1 : ℂ) else 0)) = X (v.symm i) (v.symm j)
  have hx (x : a) : i = v x ↔ x = v.symm i := by
    constructor
    · intro h; simpa only [Equiv.symm_apply_apply] using (congrArg v.symm h).symm
    · rintro rfl; simp
  have hy (y : a) : j = v y ↔ y = v.symm j := by
    constructor
    · intro h; simpa only [Equiv.symm_apply_apply] using (congrArg v.symm h).symm
    · rintro rfl; simp
  simp only [hx, hy]
  simp

theorem simulation_discard_padding (N : Channel a b) (P : Channel c d) (t : c) :
    Simulates N (N.prod P) := by
  let v : ReferenceIsometry a (a × c) :=
    ReferenceIsometry.ofInjective (fun i ↦ (i, t)) (by intro i j h; exact congrArg Prod.fst h)
  refine ⟨v, Channel.traceOutRight b d, ?_⟩
  apply channel_eq_of_single
  intro i j
  change partialTraceB ((N.prod P).map (MatrixMap.ofReferenceIsometry v
    (Matrix.single i j 1))) = N.map (Matrix.single i j 1)
  rw [show MatrixMap.ofReferenceIsometry v (Matrix.single i j 1) =
    Matrix.single (i, t) (j, t) 1 from
      MatrixMap.ofReferenceIsometry_ofInjective_single _ _ i j]
  rw [single_prod_eq_kronecker_single, Channel.prod_map_kronecker,
    partialTraceB_kronecker, P.tracePreserving]
  rw [show (Matrix.single t t (1 : ℂ)).trace = 1 by simp]
  exact matrixScale_one _

theorem simulation_tensorPower_split (N : Channel a b) (n m : ℕ) :
    Simulates ((N.tensorPower n).prod (N.tensorPower m)) (N.tensorPower (n + m)) := by
  refine ⟨ReferenceIsometry.ofEquiv (TensorPower.appendEquiv a n m),
    Channel.reindex (TensorPower.appendEquiv b n m).symm, ?_⟩
  apply channel_eq_of_map_eq
  apply matrixMap_eq_of_kronecker
  intro X Y
  change (Channel.reindex _).map ((N.tensorPower (n + m)).map
    ((Channel.reindex (TensorPower.appendEquiv a n m)).map (X.kronecker Y))) = _
  rw [channel_reindex_map, channel_reindex_map, Channel.prod_map_kronecker]
  ext i j
  rw [Matrix.submatrix_apply, Equiv.symm_symm,
    Channel.tensorPower_append_map_kronecker_apply]
  change (N.tensorPower n).map X ((TensorPower.appendEquiv b n m).symm (TensorPower.appendEquiv b n m i)).1
      ((TensorPower.appendEquiv b n m).symm (TensorPower.appendEquiv b n m j)).1 *
    (N.tensorPower m).map Y ((TensorPower.appendEquiv b n m).symm (TensorPower.appendEquiv b n m i)).2
      ((TensorPower.appendEquiv b n m).symm (TensorPower.appendEquiv b n m j)).2 = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem simulation_tensorPower_pad [Nonempty a] (N : Channel a b) (n L : ℕ) (hn : n ≤ L) :
    Simulates (N.tensorPower n) (N.tensorPower L) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have : Nonempty (QIT.TensorPower a m) := tensorPower_nonempty_of_nonempty _
  exact (simulation_discard_padding (N.tensorPower n) (N.tensorPower m)
    (Classical.arbitrary (QIT.TensorPower a m))).trans (simulation_tensorPower_split N n m)

theorem simulation_tensorPower_pair (N : Channel a b) (M : Channel c d) (n : ℕ) :
    Simulates ((N.tensorPower n).prod (M.tensorPower n)) ((N.prod M).tensorPower n) := by
  refine ⟨ReferenceIsometry.ofEquiv (tensorPowerProdEquiv a c n).symm,
    Channel.reindex (tensorPowerProdEquiv b d n), ?_⟩
  apply channel_eq_of_single
  intro i j
  change (Channel.reindex _).map (((N.prod M).tensorPower n).map
    ((Channel.reindex (tensorPowerProdEquiv a c n).symm).map (Matrix.single i j 1))) = _
  rw [channel_reindex_map (tensorPowerProdEquiv a c n).symm, Matrix.submatrix_single_equiv,
    channel_reindex_map, single_prod_eq_kronecker_single, Channel.prod_map_kronecker]
  ext x y
  rw [Matrix.submatrix_apply, Channel.tensorPower_map_single_apply]
  change _ = (N.tensorPower n).map (Matrix.single i.1 j.1 1) x.1 y.1 *
    (M.tensorPower n).map (Matrix.single i.2 j.2 1) x.2 y.2
  rw [Channel.tensorPower_map_single_apply, Channel.tensorPower_map_single_apply,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [single_prod_eq_kronecker_single, Channel.prod_map_kronecker]
  have hf (z : QIT.TensorPower a n × QIT.TensorPower c n) :
      (tensorPowerEquiv n ((tensorPowerProdEquiv a c n).symm z) k).1 =
        tensorPowerEquiv n z.1 k := by
    simpa only [Equiv.apply_symm_apply] using
      (TensorPower.tensorPowerProdEquiv_fst n ((tensorPowerProdEquiv a c n).symm z) k).symm
  have hs (z : QIT.TensorPower a n × QIT.TensorPower c n) :
      (tensorPowerEquiv n ((tensorPowerProdEquiv a c n).symm z) k).2 =
        tensorPowerEquiv n z.2 k := by
    simpa only [Equiv.apply_symm_apply] using
      (TensorPower.tensorPowerProdEquiv_snd n ((tensorPowerProdEquiv a c n).symm z) k).symm
  have hf' (z : QIT.TensorPower b n × QIT.TensorPower d n) :
      (tensorPowerEquiv n ((tensorPowerProdEquiv b d n).symm z) k).1 =
        tensorPowerEquiv n z.1 k := by
    simpa only [Equiv.apply_symm_apply] using
      (TensorPower.tensorPowerProdEquiv_fst n ((tensorPowerProdEquiv b d n).symm z) k).symm
  have hs' (z : QIT.TensorPower b n × QIT.TensorPower d n) :
      (tensorPowerEquiv n ((tensorPowerProdEquiv b d n).symm z) k).2 =
        tensorPowerEquiv n z.2 k := by
    simpa only [Equiv.apply_symm_apply] using
      (TensorPower.tensorPowerProdEquiv_snd n ((tensorPowerProdEquiv b d n).symm z) k).symm
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Equiv.symm_symm, hf, hs, hf', hs']

end QuanIncapacity
