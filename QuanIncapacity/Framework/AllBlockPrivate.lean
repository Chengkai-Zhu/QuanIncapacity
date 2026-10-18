import QuanIncapacity.Framework.TensorOrder
import QuanIncapacity.Framework.InformationOrder

/-! Zero optimized private information at every blocklength, and its
operational consequence under exactly the private coding theorem. -/

noncomputable section
open QIT

namespace QuanIncapacity

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
variable [Nonempty a] [Nonempty b] [Nonempty e]

theorem CompleteRelativeEntropyOrder.privateOneShot_tensorPower_eq_zero
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M) (n : ℕ) :
    Information.privateOneShot (N.tensorPower n) (M.tensorPower n) = 0 := by
  haveI : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty n
  exact (h.tensorPower n).privateOneShot_eq_zero

theorem CompleteRelativeEntropyOrder.regularizedPrivate_eq_zero
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M) :
    Information.regularizedPrivate N M = 0 := by
  have hv : Information.regularizedPrivateValues N M = {0} := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp only [h.privateOneShot_tensorPower_eq_zero, zero_div, Set.mem_singleton_iff]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨1, by omega, by simp only [h.privateOneShot_tensorPower_eq_zero, zero_div]⟩
  simp only [Information.regularizedPrivate, hv, csSup_singleton]

theorem CompleteRelativeEntropyOrder.privateCapacity_eq_zero
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) (coding : External.PrivateCoding N M) :
    PrivateCoding.capacity N M = 0 := by
  rw [coding hc, h.regularizedPrivate_eq_zero]

end QuanIncapacity
