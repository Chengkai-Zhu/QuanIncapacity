import QuanIncapacity.Framework.InformationSuperadditivity
import QuanIncapacity.Framework.SuperadditiveLimit

/-! The general private/coherent rate limits equal their supremum
regularizations; operational equalities remain separately named coding contracts. -/
noncomputable section
open QIT Filter
open scoped Topology

namespace QuanIncapacity
variable {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

theorem Information.private_rate_tendsto (N : Channel a b) (M : Channel a e) :
    Tendsto (fun n : ℕ ↦ privateOneShot (N.tensorPower n) (M.tensorPower n) / n)
      atTop (𝓝 (regularizedPrivate N M)) := by
  have hset : positiveBlockRates
      (fun n ↦ privateOneShot (N.tensorPower n) (M.tensorPower n)) =
      regularizedPrivateValues N M := rfl
  simpa only [hset, regularizedPrivate] using
    superadditive_rate_tendsto (private_superadditive N M)
      (hset ▸ regularizedPrivateValues_bddAbove N M)

theorem coherent_rate_tendsto (N : Channel a b) :
    Tendsto (fun n : ℕ ↦ (N.tensorPower n).coherentInformation / n)
      atTop (𝓝 N.regularizedCoherentInformation) := by
  have hset : positiveBlockRates (fun n ↦ (N.tensorPower n).coherentInformation) =
      N.regularizedCoherentInformationValues := rfl
  simpa only [hset, Channel.regularizedCoherentInformation] using
    superadditive_rate_tendsto (coherent_superadditive N)
      (hset ▸ N.regularizedCoherentInformationValues_bddAbove)

theorem privateCapacity_rate_tendsto {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) (coding : External.PrivateCoding N M) :
    Tendsto (fun n : ℕ ↦ Information.privateOneShot (N.tensorPower n) (M.tensorPower n) / n)
      atTop (𝓝 (PrivateCoding.capacity N M)) := by
  rw [coding hc]
  exact Information.private_rate_tendsto N M

theorem quantumCapacity_rate_tendsto {N : Channel a b} (coding : External.QuantumCoding N) :
    Tendsto (fun n : ℕ ↦ (N.tensorPower n).coherentInformation / n)
      atTop (𝓝 N.quantumCapacity) := by
  rw [coding]
  exact coherent_rate_tendsto N

end QuanIncapacity
