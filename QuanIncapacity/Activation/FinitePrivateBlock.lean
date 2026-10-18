import QuanIncapacity.Activation.PrivateCodeBounds

/-! A finite positive coherent-information block from positive operational
private capacity. The auxiliary dimension is chosen only after this block;
no bound on its growth is used. -/

noncomputable section
open QIT

namespace QuanIncapacity

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem PrivateCoding.exists_pos_rate {N : Channel a b} {M : Channel a e}
    (hP : 0 < PrivateCoding.capacity N M) :
    ∃ R : ℝ, 0 < R ∧ PrivateCoding.IsAchievable N M R := by
  classical
  let S := {R : ℝ | PrivateCoding.IsAchievable N M R}
  have hne : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    change 0 < sSup S at hP
    rw [he, Real.sSup_empty] at hP
    exact lt_irrefl _ hP
  by_contra h
  push Not at h
  have hb : sSup S ≤ 0 := csSup_le hne (fun R hR ↦ le_of_not_gt (fun hp ↦ h R hp hR))
  exact (not_le_of_gt hP) hb

theorem PrivateCoding.exists_large_reliable_private_code {N : Channel a b} {M : Channel a e}
    (hP : 0 < PrivateCoding.capacity N M) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ, ∃ (_ : NeZero k), ∃ C : HSWClassicalCode N n (Fin k),
      32 ≤ log2 (k : ℝ) ∧ C.toPackingDecoderCode.averageError ≤ (1 / 64 : ℝ) ∧
        PrivateCoding.leakage M C ≤ (1 / 64 : ℝ) := by
  obtain ⟨R, hR, hach⟩ := PrivateCoding.exists_pos_rate hP
  obtain ⟨n₀, hn₀⟩ := hach (R / 2) (by positivity) (1 / 64) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (64 / R)
  let n := max n₀ (m + 1)
  have hmn : m < n := (Nat.lt_succ_self m).trans_le (le_max_right _ _)
  have hn : 0 < n := (Nat.zero_le m).trans_lt hmn
  obtain ⟨k, hk, C, hrate, herr, hleak⟩ := hn₀ n (le_max_left _ _) hn
  refine ⟨n, hn, k, hk, C, ?_, herr, hleak⟩
  have hnR : 64 < (n : ℝ) * R := (div_lt_iff₀ hR).mp (hm.trans (by exact_mod_cast hmn))
  have hrate' : R / 2 ≤ log2 (k : ℝ) / n := by
    simpa only [HSWClassicalCode.rate, hswMessageRate, ne_of_gt hn, ↓reduceIte, Fintype.card_fin, sub_half] using hrate
  have hl := (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mp hrate'
  nlinarith

namespace Activation

def codeConversionValue {N : Channel a b} {n k : ℕ} [NeZero k]
    (C : HSWClassicalCode N n (Fin k)) : ℝ :=
  ((N.tensorPower n).prod
    (DephasedErasure.channel (a := Auxiliary (uniformEnsemble (Fin k) C.encoder))
      (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num))).coherentInformationFor
        (globalPurification (uniformEnsemble (Fin k) C.encoder))

theorem codeConversionValue_pos {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) {n k : ℕ} [NeZero k]
    (C : HSWClassicalCode N n (Fin k))
    (hk : 32 ≤ log2 (k : ℝ)) (herr : C.toPackingDecoderCode.averageError ≤ (1 / 64 : ℝ))
    (hleak : PrivateCoding.leakage M C ≤ (1 / 64 : ℝ)) :
    0 < codeConversionValue C := by
  have hh := private_to_coherent_bound (hc.tensorPower n) (uniformEnsemble (Fin k) C.encoder)
    (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb := code_receiver_conditionalEntropy_le N n C herr (by norm_num) (by norm_num)
  rw [uniform_output_conditionalEntropy, Fintype.card_fin] at hh
  change (1 / 4 : ℝ) * (1 / 4) * (log2 (k : ℝ) - PrivateCoding.leakage M C) -
      (1 / 4) * binaryEntropy (1 / 4) -
      (1 - 1 / 4) * (Ensemble.mapChannel (N.tensorPower n)
        (uniformEnsemble (Fin k) C.encoder)).cqState.conditionalEntropy ≤ codeConversionValue C at hh
  simp only [Fintype.card_fin] at hb
  have he := binaryEntropy_le_one (1 / 64)
  have hq := binaryEntropy_le_one (1 / 4)
  linarith

/-- A single finite code and a single finite auxiliary register give positive
coherent information before any equal-block padding is considered. -/
theorem exists_finite_positive_block {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (hP : 0 < PrivateCoding.capacity N M) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ, ∃ (_ : NeZero k), ∃ C : HSWClassicalCode N n (Fin k),
      0 < codeConversionValue C := by
  obtain ⟨n, hn, k, hk, C, hK, herr, hleak⟩ := PrivateCoding.exists_large_reliable_private_code hP
  exact ⟨n, hn, k, hk, C, codeConversionValue_pos hc C hK herr hleak⟩

end Activation
end QuanIncapacity
