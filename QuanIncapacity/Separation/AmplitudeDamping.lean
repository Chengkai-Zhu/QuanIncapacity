import QuanIncapacity.Framework.SupportCriterion
import QuanIncapacity.Framework.CoherentProcessing
import QuanIncapacity.Framework.ChannelTensorTransport
import QIT.Information.Entropy.BinaryEntropy
import QIT.Information.Entropy.MaximallyMixed

/-! Actual amplitude-damping channels, a common two-dimensional environment,
and the manuscript's counterexample to unbiased reconstruction alone. -/

noncomputable section
open QIT
open scoped Matrix BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.AmplitudeDamping

theorem sqrt_square (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
  exact_mod_cast Real.sq_sqrt hx

def kraus (γ : ℝ) : Fin 2 → CMatrix (Fin 2)
  | 0 => Matrix.diagonal ![1, (Real.sqrt (1 - γ) : ℂ)]
  | 1 => !![0, (Real.sqrt γ : ℂ); 0, 0]

theorem kraus_complete (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ∑ l : Fin 2, (kraus γ l).conjTranspose * kraus γ l = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kraus, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal, Matrix.one_apply]
  ring_nf
  rw [sqrt_square γ h0, sqrt_square (1 - γ) (sub_nonneg.mpr h1)]
  push_cast
  ring

theorem tracePreserving (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    MatrixMap.IsTracePreserving (MatrixMap.ofKraus (kraus γ)) :=
  MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using kraus_complete γ h0 h1)

def channel (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) : Channel (Fin 2) (Fin 2) where
  map := MatrixMap.ofKraus (kraus γ)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := tracePreserving γ h0 h1
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem channel_apply (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (X : CMatrix (Fin 2)) :
    (channel γ h0 h1).map X =
      !![X 0 0 + (γ : ℂ) * X 1 1, (Real.sqrt (1 - γ) : ℂ) * X 0 1;
        (Real.sqrt (1 - γ) : ℂ) * X 1 0, (1 - (γ : ℂ)) * X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [channel, MatrixMap.ofKraus, kraus, Fin.sum_univ_two,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Matrix.diagonal]
  all_goals ring_nf
  all_goals simp only [sqrt_square γ h0, sqrt_square (1 - γ) (sub_nonneg.mpr h1)]
  all_goals push_cast
  all_goals ring

def dilation (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ReferenceIsometry (Fin 2) (Fin 2 × Fin 2) :=
  MatrixMap.krausStinespringIsometry (kraus γ) (tracePreserving γ h0 h1)

theorem complement_eq (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (dilation γ h0 h1).complementaryChannel =
      channel (1 - γ) (sub_nonneg.mpr h1) (by linarith) := by
  apply channel_eq_of_map_eq
  ext X i j
  change (MatrixMap.krausStinespringIsometry (kraus γ)
    (tracePreserving γ h0 h1)).complementaryChannel.map X i j = _
  rw [Stinespring.complementary_kraus_map, channel_apply]
  have hg : 1 - (1 - γ) = γ := by ring
  fin_cases i <;> fin_cases j <;>
    norm_num [kraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace,
      Matrix.diagonal, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hg]
  all_goals ring_nf
  all_goals simp only [sqrt_square γ h0, sqrt_square (1 - γ) (sub_nonneg.mpr h1)]
  all_goals push_cast
  all_goals ring

theorem complementary (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ComplementaryChannels (channel γ h0 h1)
      (channel (1 - γ) (sub_nonneg.mpr h1) (by linarith)) := by
  refine ⟨dilation γ h0 h1, ?_, complement_eq γ h0 h1⟩
  apply ReferenceIsometry.outputChannel_eq_of_realizes
  intro X
  exact (MatrixMap.partialTraceB_krausStinespringIsometry (kraus γ)
    (tracePreserving γ h0 h1) X).symm

def shadow (γ : ℝ) : MatrixMap (Fin 2) (Fin 2) where
  toFun Y :=
    !![Y 0 0, ((Real.sqrt (1 - γ) / Real.sqrt γ : ℝ) : ℂ) * Y 0 1;
      ((Real.sqrt (1 - γ) / Real.sqrt γ : ℝ) : ℂ) * Y 1 0,
      (((2 * γ - 1) / γ : ℝ) : ℂ) * Y 0 0 + (((1 - γ) / γ : ℝ) : ℂ) * Y 1 1]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply] <;> ring
  map_smul' z X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, smul_eq_mul] <;> ring

theorem shadow_unbiased (γ : ℝ) (h0 : 0 < γ) (h1 : γ ≤ 1) :
    Shadowing.IsUnbiasedShadow (channel γ h0.le h1).map
      (channel (1 - γ) (sub_nonneg.mpr h1) (by linarith)).map (shadow γ) := by
  constructor
  · intro Y
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shadow, Matrix.conjTranspose_apply, map_add, map_mul]
  · intro X Y
    rw [channel_apply, channel_apply]
    have hγ : (γ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
    have hs : (Real.sqrt γ : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr h0)
    have hg : 1 - (1 - γ) = γ := by ring
    simp [shadow, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hg]
    push_cast
    field_simp
    ring

theorem maximallyMixed_output (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ((channel γ h0 h1).applyState (State.maximallyMixed (Fin 2))).matrix =
      Matrix.diagonal (fun i : Fin 2 ↦ ((if i = 0 then (1 + γ) / 2 else (1 - γ) / 2 : ℝ) : ℂ)) := by
  change (channel γ h0 h1).map (State.maximallyMixed (Fin 2)).matrix = _
  rw [channel_apply, State.maximallyMixed_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal]
  all_goals push_cast
  all_goals ring

theorem maximallyMixed_entropy (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    ((channel γ h0 h1).applyState (State.maximallyMixed (Fin 2))).vonNeumann =
      binaryEntropy ((1 - γ) / 2) := by
  rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal _ _ (maximallyMixed_output γ h0 h1)]
  simp only [Fin.sum_univ_two, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    binaryEntropy]
  rw [show 1 - (1 - γ) / 2 = (1 + γ) / 2 by ring]
  ring

theorem coherent_eq (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    Information.coherent (channel γ h0 h1)
      (channel (1 - γ) (sub_nonneg.mpr h1) (by linarith)) (State.maximallyMixed (Fin 2)) =
      binaryEntropy ((1 - γ) / 2) - binaryEntropy (γ / 2) := by
  unfold Information.coherent
  rw [maximallyMixed_entropy, maximallyMixed_entropy,
    show 1 - (1 - γ) = γ by ring]

theorem coherent_pos (γ : ℝ) (h0 : 0 < γ) (hhalf : γ < 1 / 2) :
    0 < Information.coherent (channel γ h0.le (by linarith))
      (channel (1 - γ) (by linarith) (by linarith)) (State.maximallyMixed (Fin 2)) := by
  rw [coherent_eq, sub_pos,
    binaryEntropy_eq_binEntropy_div_log_two, binaryEntropy_eq_binEntropy_div_log_two]
  apply (div_lt_div_iff_of_pos_right (Real.log_pos one_lt_two)).mpr
  apply Real.binEntropy_strictMonoOn
  · constructor <;> linarith
  · constructor <;> linarith
  · linarith

theorem no_complete_shadow (γ : ℝ) (h0 : 0 < γ) (hhalf : γ < 1 / 2)
    (J : MatrixMap (Fin 2) (Fin 2)) :
    ¬ Shadowing.IsCompleteShadow (channel γ h0.le (by linarith)).map
      (channel (1 - γ) (by linarith) (by linarith)).map J := by
  intro h
  have hn := (Shadowing.complete_relativeEntropy_order_of_shadow _ _ _ h).coherent_nonpos
    (complementary γ h0.le (by linarith)) (State.maximallyMixed (Fin 2))
  exact (not_le_of_gt (coherent_pos γ h0 hhalf)) hn

end QuanIncapacity.AmplitudeDamping
