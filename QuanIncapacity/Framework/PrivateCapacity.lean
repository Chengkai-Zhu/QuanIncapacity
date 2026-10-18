import QuanIncapacity.Framework.ChannelPair
import QuanIncapacity.Framework.Capacities
import QIT.Coding.Classical.RandomnessDistribution
import QIT.Coding.Quantum.Basic
import QIT.Information.Entropy.CoherentInformation

/-!
# Information quantities, operational private capacity, and coding contracts

Messages are uniform. Reliability is average decoding error; strong secrecy
requires the unnormalized Holevo leakage to tend to zero. The decoder is an
actual POVM and the encoder may use mixed states entangled across the block.
The coding equalities below are *types of external theorems*, not proofs,
global axioms, or definitions that rename information quantities as capacities.
-/

noncomputable section
open scoped BigOperators
open QIT

namespace QuanIncapacity

variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

namespace Information

def coherent (N : Channel a b) (M : Channel a e) (ρ : State a) : ℝ :=
  (N.applyState ρ).vonNeumann - (M.applyState ρ).vonNeumann

def privateInfo {ι : Type} [Fintype ι] (N : Channel a b) (M : Channel a e)
    (E : Ensemble ι a) : ℝ :=
  (Ensemble.mapChannel N E).holevoInformation - (Ensemble.mapChannel M E).holevoInformation

def privateValues (N : Channel a b) (M : Channel a e) : Set ℝ :=
  {x | ∃ k : ℕ, ∃ E : Ensemble (Fin k) a, privateInfo N M E = x}

def privateOneShot (N : Channel a b) (M : Channel a e) : ℝ :=
  sSup (privateValues N M)

def regularizedPrivateValues (N : Channel a b) (M : Channel a e) : Set ℝ :=
  {x | ∃ n : ℕ, 0 < n ∧ x = privateOneShot (N.tensorPower n) (M.tensorPower n) / n}

def regularizedPrivate (N : Channel a b) (M : Channel a e) : ℝ :=
  sSup (regularizedPrivateValues N M)

end Information

namespace PrivateCoding

variable {N : Channel a b} {n : ℕ} {k : ℕ} [NeZero k]

/-- Uniform-message strong-secrecy leakage to the entire environment. -/
def leakage (M : Channel a e) (C : HSWClassicalCode N n (Fin k)) : ℝ :=
  (Ensemble.mapChannel (M.tensorPower n) (uniformEnsemble (Fin k) C.encoder)).holevoInformation

/-- An operational rate requires reliable, strongly secret codes at every
sufficiently large positive blocklength, for every positive rate slack. -/
def IsAchievable (N : Channel a b) (M : Channel a e) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ → 0 < n →
      ∃ k : ℕ, ∃ (_ : NeZero k), ∃ C : HSWClassicalCode N n (Fin k),
        R - δ ≤ C.rate ∧ C.toPackingDecoderCode.averageError ≤ ε ∧ leakage M C ≤ ε

def capacity (N : Channel a b) (M : Channel a e) : ℝ :=
  sSup {R : ℝ | IsAchievable N M R}

theorem IsAchievable.mono {M : Channel a e} {R S : ℝ}
    (hS : IsAchievable N M S) (hRS : R ≤ S) : IsAchievable N M R := by
  intro δ hδ ε hε
  obtain ⟨n₀, hn₀⟩ := hS δ hδ ε hε
  refine ⟨n₀, fun n hn hpos ↦ ?_⟩
  obtain ⟨k, hk, C, hrate, herr, hleak⟩ := hn₀ n hn hpos
  exact ⟨k, hk, C, (sub_le_sub_right hRS δ).trans hrate, herr, hleak⟩

end PrivateCoding

namespace External

/-- Permitted external quantum coding theorem, with the upstream operational
capacity and its independently defined regularized coherent information. -/
def QuantumCoding (N : Channel a b) : Prop :=
  N.quantumCapacity = N.regularizedCoherentInformation

/-- Permitted external private coding theorem. The complementarity premise
must be supplied from a common Stinespring isometry. -/
def PrivateCoding (N : Channel a b) (M : Channel a e) : Prop :=
  ComplementaryChannels N M →
    QuanIncapacity.PrivateCoding.capacity N M = Information.regularizedPrivate N M

end External
end QuanIncapacity
