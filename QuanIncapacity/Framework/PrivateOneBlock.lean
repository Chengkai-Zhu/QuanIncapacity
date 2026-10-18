import QuanIncapacity.Framework.PrivateOptimization

/-! The zero-use unit factor in Lean-QIT's recursive tensor powers is
handled explicitly when introducing a positive one-use private rate. -/

noncomputable section
open QIT
open scoped Matrix BigOperators

namespace QuanIncapacity.Information

set_option backward.isDefEq.respectTransparency false

variable {a b e ι : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
variable [Fintype ι]

omit [Nonempty a] in
def appendUnit (E : QIT.Ensemble ι a) : QIT.Ensemble ι (a × PUnit.{1}) where
  probs := E.probs
  weights_sum := E.weights_sum
  states i := (E.states i).prod State.unit

omit [Nonempty a] in
theorem appendUnit_average (E : QIT.Ensemble ι a) :
    (appendUnit E).averageState = E.averageState.prod State.unit := by
  apply State.ext
  simp only [QIT.Ensemble.averageState_matrix, appendUnit, State.prod_matrix_kronecker]
  ext ⟨i, ⟨⟩⟩ ⟨j, ⟨⟩⟩
  simp [Matrix.sum_apply, Matrix.smul_apply, State.unit, Matrix.kronecker]

omit [Nonempty a] in
theorem tensorPower_one_apply (N : Channel a b) (ρ : State a) :
    (N.tensorPower 1).applyState (ρ.prod State.unit) = (N.applyState ρ).prod State.unit := by
  change (N.prod Channel.unit).applyState (ρ.prod State.unit) = _
  rw [Channel.applyState_prod]
  have he : (Channel.unit : Channel PUnit.{1} PUnit.{1}).applyState State.unit = State.unit := by
    apply State.ext
    ext i j
    cases i
    cases j
    rfl
  rw [he]

omit [Nonempty a] in
theorem map_appendUnit (N : Channel a b) (E : QIT.Ensemble ι a) :
    Ensemble.mapChannel (N.tensorPower 1) (appendUnit E) = appendUnit (Ensemble.mapChannel N E) := by
  have hs : ∀ i, (N.tensorPower 1).applyState ((E.states i).prod State.unit) =
      (N.applyState (E.states i)).prod State.unit := fun i ↦ tensorPower_one_apply N (E.states i)
  cases E
  unfold Ensemble.mapChannel appendUnit
  congr 1
  funext i
  exact hs i

omit [Nonempty a] in
theorem appendUnit_holevo (E : QIT.Ensemble ι a) :
    (appendUnit E).holevoInformation = E.holevoInformation := by
  rw [QIT.Ensemble.holevoInformation_def, appendUnit_average, State.vonNeumann_prod,
    QIT.Ensemble.holevoInformation_def]
  change E.averageState.vonNeumann + State.unit.vonNeumann -
    ∑ i, (E.probs i : ℝ) * ((E.states i).prod State.unit).vonNeumann = _
  simp only [State.vonNeumann_prod, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  have hp : ∑ i, (E.probs i : ℝ) = 1 := by exact_mod_cast E.weights_sum
  rw [hp, one_mul]
  ring

omit [Nonempty a] in
theorem privateInfo_one_block (N : Channel a b) (M : Channel a e) (E : QIT.Ensemble ι a) :
    privateInfo (N.tensorPower 1) (M.tensorPower 1) (appendUnit E) = privateInfo N M E := by
  change (Ensemble.mapChannel (N.tensorPower 1) (appendUnit E)).holevoInformation -
    (Ensemble.mapChannel (M.tensorPower 1) (appendUnit E)).holevoInformation =
      (Ensemble.mapChannel N E).holevoInformation - (Ensemble.mapChannel M E).holevoInformation
  rw [map_appendUnit, map_appendUnit, appendUnit_holevo, appendUnit_holevo]

theorem privateOneShot_le_regularized (N : Channel a b) (M : Channel a e) :
    privateOneShot N M ≤ regularizedPrivate N M := by
  have : Nonempty (QIT.TensorPower a 1) := tensorPower_nonempty_of_nonempty _
  apply csSup_le ⟨0, zero_mem_privateValues N M⟩
  rintro x ⟨k, E, rfl⟩
  have hb := privateInfo_le_oneShot (N.tensorPower 1) (M.tensorPower 1) (appendUnit E)
  rw [privateInfo_one_block] at hb
  exact hb.trans (by
    simpa only [Nat.cast_one, div_one] using block_private_rate_le_regularized N M 1 (by omega))

theorem privateOneShot_le_capacity {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (coding : External.PrivateCoding N M) :
    privateOneShot N M ≤ PrivateCoding.capacity N M := by
  rw [coding hc]
  exact privateOneShot_le_regularized N M

theorem privateCapacity_pos_of_ensemble {k : ℕ} {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (coding : External.PrivateCoding N M)
    (E : QIT.Ensemble (Fin k) a) (hE : 0 < privateInfo N M E) :
    0 < PrivateCoding.capacity N M := by
  rw [coding hc]
  have h : 0 < privateOneShot (N.tensorPower 1) (M.tensorPower 1) := by
    have : Nonempty (QIT.TensorPower a 1) := tensorPower_nonempty_of_nonempty _
    have hb := privateInfo_le_oneShot (N.tensorPower 1) (M.tensorPower 1) (appendUnit E)
    rw [privateInfo_one_block] at hb
    exact hE.trans_le hb
  simpa only [Nat.cast_one, div_one] using h.trans_le (by
    simpa only [Nat.cast_one, div_one] using block_private_rate_le_regularized N M 1 (by omega))

end QuanIncapacity.Information
