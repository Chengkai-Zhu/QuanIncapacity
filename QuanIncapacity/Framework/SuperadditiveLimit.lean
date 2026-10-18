import Mathlib.Analysis.Subadditive

/-! Supremum form of Fekete's lemma, including an arbitrary zero-use value. -/
noncomputable section
open Set Filter
open scoped Topology

namespace QuanIncapacity

def positiveBlockRates (u : ℕ → ℝ) : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ r = u n / n}

theorem superadditive_rate_tendsto {u : ℕ → ℝ}
    (hu : ∀ m n, u m + u n ≤ u (m + n))
    (hb : BddAbove (positiveBlockRates u)) :
    Tendsto (fun n : ℕ ↦ u n / n) atTop (𝓝 (sSup (positiveBlockRates u))) := by
  have hs : Subadditive (fun n ↦ -u n) := by
    intro m n
    dsimp
    linarith [hu m n]
  obtain ⟨C, hC⟩ := hb
  have hbneg : BddBelow (range fun n : ℕ ↦ -u n / n) := by
    refine ⟨-max C 0, ?_⟩
    rintro x ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact neg_nonpos.mpr (le_max_right _ _)
    · have h := hC (show u n / n ∈ positiveBlockRates u from ⟨n, Nat.pos_of_ne_zero hn, rfl⟩)
      dsimp only
      rw [neg_div]
      linarith [le_max_left C 0]
  have hp : (positiveBlockRates u).Nonempty := ⟨u 1 / 1, 1, by omega, by simp⟩
  have hi : hs.lim = -sSup (positiveBlockRates u) := by
    apply le_antisymm
    · have hsup : sSup (positiveBlockRates u) ≤ -hs.lim := by
        apply csSup_le hp
        rintro x ⟨n, hn, rfl⟩
        have h := hs.lim_le_div hbneg hn.ne'
        rw [neg_div] at h
        linarith
      linarith
    · rw [Subadditive.lim]
      apply le_csInf (by exact ⟨(fun n : ℕ ↦ -u n / (n : ℝ)) 1, 1, by simp, rfl⟩)
      rintro x ⟨n, hn, rfl⟩
      have h := le_csSup ⟨C, hC⟩
        (show u n / n ∈ positiveBlockRates u from ⟨n, lt_of_lt_of_le Nat.zero_lt_one (show 1 ≤ n from hn), rfl⟩)
      dsimp only
      rw [neg_div]
      exact neg_le_neg h
  have ht := hs.tendsto_lim hbneg
  rw [hi] at ht
  have ht' := ht.neg
  simpa only [neg_div, neg_neg] using ht'

end QuanIncapacity
