import QuanIncapacity.Framework.InformationOrder
import QuanIncapacity.Framework.ComplementaryTensor

/-! Bounds for the actual private-information optimization and a bridge
from positive one-shot ensemble information to operational private capacity. -/

noncomputable section
open QIT
open scoped Matrix BigOperators

namespace QuanIncapacity.Information

variable {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem privateInfo_le_log_card {ι : Type} [Fintype ι] (N : Channel a b) (M : Channel a e)
    (E : QIT.Ensemble ι a) : privateInfo N M E ≤ log2 (Fintype.card b) := by
  classical
  have hn : 0 ≤ (Ensemble.mapChannel M E).holevoInformation := by
    rw [← cqState_mutualInformation_eq_holevoInformation]
    exact State.mutualInformation_nonneg _
  exact (sub_le_self _ hn).trans (QIT.Ensemble.holevo_le_log_card _)

theorem privateValues_bddAbove (N : Channel a b) (M : Channel a e) :
    BddAbove (privateValues N M) := by
  refine ⟨log2 (Fintype.card b), ?_⟩
  rintro x ⟨k, E, rfl⟩
  exact privateInfo_le_log_card N M E

theorem privateInfo_le_oneShot {k : ℕ} (N : Channel a b) (M : Channel a e)
    (E : QIT.Ensemble (Fin k) a) : privateInfo N M E ≤ privateOneShot N M :=
  le_csSup (privateValues_bddAbove N M) ⟨k, E, rfl⟩

theorem privateOneShot_le_log_card (N : Channel a b) (M : Channel a e) :
    privateOneShot N M ≤ log2 (Fintype.card b) := by
  apply csSup_le ⟨0, zero_mem_privateValues N M⟩
  rintro x ⟨k, E, rfl⟩
  exact privateInfo_le_log_card N M E

theorem private_block_rate_le_log_card (N : Channel a b) (M : Channel a e)
    (n : ℕ) (hn : 0 < n) :
    privateOneShot (N.tensorPower n) (M.tensorPower n) / (n : ℝ) ≤ log2 (Fintype.card b) := by
  have : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty _
  apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
  calc
    _ ≤ log2 (Fintype.card (QIT.TensorPower b n)) := privateOneShot_le_log_card _ _
    _ = log2 (Fintype.card b) * (n : ℝ) := by
      rw [tensorPower_card, Nat.cast_pow]
      unfold log2
      rw [Real.log_pow]
      ring

theorem regularizedPrivateValues_bddAbove (N : Channel a b) (M : Channel a e) :
    BddAbove (regularizedPrivateValues N M) := by
  refine ⟨log2 (Fintype.card b), ?_⟩
  rintro x ⟨n, hn, rfl⟩
  exact private_block_rate_le_log_card N M n hn

theorem block_private_rate_le_regularized (N : Channel a b) (M : Channel a e)
    (n : ℕ) (hn : 0 < n) :
    privateOneShot (N.tensorPower n) (M.tensorPower n) / (n : ℝ) ≤ regularizedPrivate N M :=
  le_csSup (regularizedPrivateValues_bddAbove N M) ⟨n, hn, rfl⟩

end QuanIncapacity.Information
