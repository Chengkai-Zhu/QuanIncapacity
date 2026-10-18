import QuanIncapacity.Activation.PrivateToCoherent
import QIT.Information.Entropy.BinaryEntropy

/-! Reliability uses average error, as in the operational private-code
definition. The Fano estimate is proved for that error, without expurgating
messages or changing the environment's leakage. -/

noncomputable section
open QIT
open scoped BigOperators NNReal

namespace QuanIncapacity.Activation

variable {a b e ι : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
variable [Fintype ι] [DecidableEq ι]

theorem cq_conditionalEntropy (E : Ensemble ι a) :
    E.cqState.conditionalEntropy = classicalEntropy E.probs - E.holevoInformation := by
  rw [State.conditionalEntropy_eq, State.cqState_vonNeumann,
    Ensemble.cqState_marginalB_eq_averageState, Ensemble.holevoInformation_def]
  unfold classicalEntropy
  ring

theorem uniform_output_conditionalEntropy [Nonempty ι] (N : Channel a b) (ρ : ι → State a) :
    (Ensemble.mapChannel N (uniformEnsemble ι ρ)).cqState.conditionalEntropy =
      log2 (Fintype.card ι : ℝ) - (Ensemble.mapChannel N (uniformEnsemble ι ρ)).holevoInformation := by
  rw [cq_conditionalEntropy]
  have he : (Ensemble.mapChannel N (uniformEnsemble ι ρ)).probs = uniformMessageProb (M := ι) := rfl
  rw [he, classicalEntropy_uniformMessageProb]

theorem decoded_averageError [Nonempty ι] (N : Channel a b) (n : ℕ)
    (C : HSWClassicalCode N n ι) :
    (decodedPairErrorProb ι (uniformDecodedMessageProb N n ι C) : ℝ) =
      C.toPackingDecoderCode.averageError := by
  have hsum : (decodedPairSuccessProb ι (uniformDecodedMessageProb N n ι C) : ℝ) +
      (decodedPairErrorProb ι (uniformDecodedMessageProb N n ι C) : ℝ) = 1 := by
    exact_mod_cast (decodedPairSuccessProb_add_errorProb ι (uniformDecodedMessageProb N n ι C)).trans
      (uniformDecodedMessageProb_sum N n ι C)
  rw [uniformDecodedMessageProb_success] at hsum
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  have he : C.toPackingDecoderCode.averageError =
      1 - ∑ m, (uniformMessageProb (M := ι) m : ℝ) * C.successProbability m := by
    unfold PackingLemma.DecoderCode.averageError PackingLemma.DecoderCode.error
    simp only [HSWClassicalCode.toPackingDecoderCode_successProbability,
      uniformMessageProb, NNReal.coe_inv, NNReal.coe_natCast,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, mul_sub, inv_mul_cancel₀ hk]
  linarith

theorem code_holevo_fano [Nonempty ι] (N : Channel a b) (n : ℕ)
    (C : HSWClassicalCode N n ι) {ε : ℝ}
    (herr : C.toPackingDecoderCode.averageError ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) * log2 (Fintype.card ι : ℝ) - binaryEntropy ε ≤
      (Ensemble.mapChannel (N.tensorPower n) (uniformEnsemble ι C.encoder)).holevoInformation := by
  have hd := decodedMessageFano ι (uniformDecodedMessageProb N n ι C)
    (uniformDecodedMessageProb_sum N n ι C) ε (uniformDecodedMessageProb_marginalA N n ι C)
    (by rw [decoded_averageError]; exact herr) hε0 hε1
  have hh := hd.trans (mutualInformation_uniformDecodedMessageState_le_cqChannelOutputState N n ι C)
  rw [cqChannelOutputState, cqState_mutualInformation_eq_holevoInformation] at hh
  change (1 - ε) * log2 (Fintype.card ι : ℝ) + xlog2 ε + xlog2 (1 - ε) ≤
    (Ensemble.mapChannel (N.tensorPower n) (uniformEnsemble ι C.encoder)).holevoInformation at hh
  unfold binaryEntropy
  linarith

theorem code_receiver_conditionalEntropy_le [Nonempty ι] (N : Channel a b) (n : ℕ)
    (C : HSWClassicalCode N n ι) {ε : ℝ}
    (herr : C.toPackingDecoderCode.averageError ≤ ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (Ensemble.mapChannel (N.tensorPower n) (uniformEnsemble ι C.encoder)).cqState.conditionalEntropy ≤
      binaryEntropy ε + ε * log2 (Fintype.card ι : ℝ) := by
  rw [uniform_output_conditionalEntropy]
  have hh := code_holevo_fano N n C herr hε0 hε1
  linarith

end QuanIncapacity.Activation
