import QuanIncapacity.Qutrit.Lambda
import QuanIncapacity.Framework.ChannelPair

noncomputable section
open QIT

namespace QuanIncapacity

def qutritStinespring : ReferenceIsometry (Fin 3) (Fin 3 × Fin 4) :=
  MatrixMap.krausStinespringIsometry K (by
    rw [← Λ_map_eq_ofKraus]
    exact Λ.tracePreserving)

theorem qutritStinespring_output : qutritStinespring.outputChannel = Λ := by
  apply ReferenceIsometry.outputChannel_eq_of_realizes
  intro X
  rw [qutritStinespring, MatrixMap.partialTraceB_krausStinespringIsometry]
  exact congrArg (fun Φ : MatrixMap (Fin 3) (Fin 3) ↦ Φ X) Λ_map_eq_ofKraus

theorem qutritStinespring_environment : qutritStinespring.complementaryChannel = Λc := by
  have hm : qutritStinespring.complementaryChannel.map = Λc.map := by
    apply LinearMap.ext
    intro X
    ext i j
    exact Stinespring.complementary_kraus_map K _ X i j
  exact channel_eq_of_map_eq _ _ hm

theorem qutrit_complementary : ComplementaryChannels Λ Λc :=
  ⟨qutritStinespring, qutritStinespring_output, qutritStinespring_environment⟩

end QuanIncapacity
