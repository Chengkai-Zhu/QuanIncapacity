import QuanIncapacity.Framework.AllBlockPrivate
import QuanIncapacity.Framework.ComplementaryInformation
import QuanIncapacity.Framework.ComplementaryTensor

/-! All-block zero information and the two separately parameterized operational
capacity conclusions. The information statements use no coding theorem. -/

noncomputable section
open QIT Filter
open scoped Topology

namespace QuanIncapacity

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
variable [Nonempty a] [Nonempty b] [Nonempty e]

theorem CompleteRelativeEntropyOrder.coherentInformation_tensorPower_eq_zero
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) (n : ℕ) : (N.tensorPower n).coherentInformation = 0 := by
  haveI : Nonempty (QIT.TensorPower a n) := tensorPower_nonempty_of_nonempty n
  exact (h.tensorPower n).coherentInformation_eq_zero (hc.tensorPower n)

theorem CompleteRelativeEntropyOrder.regularizedCoherentInformation_eq_zero
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) : N.regularizedCoherentInformation = 0 := by
  have hv : N.regularizedCoherentInformationValues = {0} := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp only [h.coherentInformation_tensorPower_eq_zero hc, zero_div, Set.mem_singleton_iff]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨1, by omega,
        by simp only [h.coherentInformation_tensorPower_eq_zero hc, zero_div]⟩
  simp only [Channel.regularizedCoherentInformation, hv, csSup_singleton]

theorem CompleteRelativeEntropyOrder.quantumCapacity_eq_zero
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) (coding : External.QuantumCoding N) :
    N.quantumCapacity = 0 := by
  rw [coding, h.regularizedCoherentInformation_eq_zero hc]

theorem CompleteRelativeEntropyOrder.private_rate_tendsto_zero
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M) :
    Tendsto (fun n : ℕ ↦ Information.privateOneShot (N.tensorPower n) (M.tensorPower n) / n)
      atTop (𝓝 0) := by
  simpa only [h.privateOneShot_tensorPower_eq_zero, zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

theorem CompleteRelativeEntropyOrder.coherent_rate_tendsto_zero
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) :
    Tendsto (fun n : ℕ ↦ (N.tensorPower n).coherentInformation / n) atTop (𝓝 0) := by
  simpa only [h.coherentInformation_tensorPower_eq_zero hc, zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

theorem CompleteRelativeEntropyOrder.private_superadditive
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M) (m n : ℕ) :
    Information.privateOneShot (N.tensorPower m) (M.tensorPower m) +
        Information.privateOneShot (N.tensorPower n) (M.tensorPower n) ≤
      Information.privateOneShot (N.tensorPower (m + n)) (M.tensorPower (m + n)) := by
  simp only [h.privateOneShot_tensorPower_eq_zero, add_zero, le_refl]

theorem CompleteRelativeEntropyOrder.coherent_superadditive
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M)
    (hc : ComplementaryChannels N M) (m n : ℕ) :
    (N.tensorPower m).coherentInformation + (N.tensorPower n).coherentInformation ≤
      (N.tensorPower (m + n)).coherentInformation := by
  simp only [h.coherentInformation_tensorPower_eq_zero hc, add_zero, le_refl]

end QuanIncapacity
