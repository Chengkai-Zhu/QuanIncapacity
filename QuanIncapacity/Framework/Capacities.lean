import QuanIncapacity.Framework.Shadowing
import QIT.Information.Entropy.Holevo

/-!
# Qutrit information quantities

Coherent and private information and their one-shot optimizations for the
qutrit channel. `Qutrit/ZeroCapacity` proves the all-block information zeros
and the operational capacity statements under their respective coding contracts.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators
open QIT

namespace QuanIncapacity

open QuanIncapacity

/- Coherent information of a qutrit input through `Λ`: `I_c(ρ, Λ) = S(Λ(ρ)) − S(Λᶜ(ρ))`. -/
noncomputable def coherentInfo (ρ : State (Fin 3)) : ℝ :=
  (Λ.applyState ρ).vonNeumann - (Λc.applyState ρ).vonNeumann

/- The one-shot coherent information `Q⁽¹⁾(Λ) = max_ρ I_c(ρ, Λ)`. -/
noncomputable def coherentInfoMax : ℝ :=
  sSup { x : ℝ | ∃ ρ : State (Fin 3), coherentInfo ρ = x }

/- Push an ensemble through a channel (apply the channel to each state). -/
noncomputable def Ensemble.mapChannel {ι a b : Type*} [Fintype ι] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (Phi : Channel a b) (E : Ensemble ι a) : Ensemble ι b where
  probs := E.probs
  weights_sum := E.weights_sum
  states i := Phi.applyState (E.states i)

/- Private information of an ensemble through `Λ`: the Holevo advantage of the receiver
  over the environment, `I(U;B) − I(U;E)`. -/
noncomputable def privateInfo {ι : Type*} [Fintype ι]
    (E : Ensemble ι (Fin 3)) : ℝ :=
  Ensemble.holevoInformation (Ensemble.mapChannel Λ E) -
    Ensemble.holevoInformation (Ensemble.mapChannel Λc E)

/- The one-shot private information `P⁽¹⁾(Λ) = sup_E [I(U;B) − I(U;E)]`. -/
noncomputable def privateInfoMax : ℝ :=
  sSup { x : ℝ | ∃ ι : Type, ∃ _ : Fintype ι, ∃ E : Ensemble ι (Fin 3), privateInfo E = x }

/-- Coherent and private information inequalities at every positive blocklength.
Proved by `qutrit_all_block_zero_information`. -/
def QutritAllBlockZeroInformation : Prop :=
  ∀ n : ℕ, 0 < n →
    (∀ ρ : State (QIT.TensorPower (Fin 3) n),
      (((Λ.tensorPower n).applyState ρ).vonNeumann -
        ((Λc.tensorPower n).applyState ρ).vonNeumann) ≤ 0) ∧
    (∀ k : ℕ, ∀ E : Ensemble (Fin k) (QIT.TensorPower (Fin 3) n),
      Ensemble.holevoInformation (Ensemble.mapChannel (Λ.tensorPower n) E) ≤
        Ensemble.holevoInformation (Ensemble.mapChannel (Λc.tensorPower n) E))

end QuanIncapacity
