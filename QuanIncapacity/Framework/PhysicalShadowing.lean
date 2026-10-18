import QuanIncapacity.Framework.Adjoint
import QuanIncapacity.Framework.OutputSupport
import QuanIncapacity.Framework.TensorOrder
import QIT.Util.SDP.HermitianPSDTraceDuality

/-! A physical degrading channel supplies the actual completely shadowing
Heisenberg adjoint, including entangled references. -/
noncomputable section
open QIT QuanIncapacity.MatrixSpace
open scoped Matrix ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.Shadowing
variable {a b e : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

private theorem amp_id {r c : Type} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c] (X : CMatrix (r × c)) :
    amp r (Channel.idChannel c).map X = X := by
  ext i j
  rw [amp_apply, idChannel_map_eq, LinearMap.id_apply]

theorem physical_unbiased (D : Channel e b) :
    IsUnbiasedShadow D.map (Channel.idChannel e).map (hsAdjoint D.map) := by
  refine ⟨hsAdjoint_map_adjoint D.map (channel_map_adjoint D), ?_⟩
  intro X Y
  have h := hsAdjoint_pairing D.map X.conjTranspose Y
  simpa only [channel_map_adjoint, Matrix.conjTranspose_conjTranspose,
    idChannel_map_eq, LinearMap.id_apply] using h

/-- Kadison--Schwarz in the actual amplified Heisenberg adjoint. -/
theorem physical_kadison (D : Channel e b) (r : Type) [Fintype r] [DecidableEq r]
    (Y : CMatrix (r × b)) (hY : Y.IsHermitian) :
    amp r (hsAdjoint D.map) Y * amp r (hsAdjoint D.map) Y ≤
      amp r (hsAdjoint D.map) (Y * Y) := by
  let DR := (Channel.idChannel r).prod D
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd DR.map DR.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact DR.tracePreserving
  have hJ (Z : CMatrix (r × b)) : amp r (hsAdjoint D.map) Z = MatrixMap.krausAdjoint K Z := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    have hm := (physical_unbiased D).amp_mean_eq X Z
    rw [amp_id] at hm
    calc
      (X * amp r (hsAdjoint D.map) Z).trace = (DR.map X * Z).trace := hm.symm
      _ = (X * MatrixMap.krausAdjoint K Z).trace := by
        rw [hK]
        exact MatrixMap.ofKraus_trace_duality K X Z
  rw [hJ, hJ]
  exact MatrixMap.krausAdjoint_mul_self_le_of_tracePreserving K hTP hY

theorem complete_shadow_of_physical (M : Channel a e) (D : Channel e b) :
    IsCompleteShadow (D.comp M).map M.map (hsAdjoint D.map) := by
  have hU : IsUnbiasedShadow (D.comp M).map M.map (hsAdjoint D.map) :=
    ⟨(physical_unbiased D).map_adjoint, fun X Y ↦ by
      change (D.map (M.map X) * Y).trace = (M.map X * hsAdjoint D.map Y).trace
      simpa only [idChannel_map_eq, LinearMap.id_apply] using
        (physical_unbiased D).mean_eq (M.map X) Y⟩
  refine ⟨hU, ?_⟩
  intro r _ _ ρ Y hY
  let τ := ((Channel.idChannel r).prod M).applyState ρ
  have hρ : (amp r M.map ρ.matrix).PosSemidef := τ.pos
  have hK := Matrix.le_iff.mp (physical_kadison D r Y hY)
  have ht := cMatrix_trace_mul_posSemidef_re_nonneg hρ hK
  have hm := hU.amp_mean_eq ρ.matrix Y
  have hsecond := (physical_unbiased D).amp_mean_eq (amp r M.map ρ.matrix) (Y * Y)
  rw [amp_id] at hsecond
  have hcomp : amp r D.map (amp r M.map ρ.matrix) = amp r (D.comp M).map ρ.matrix := by
    exact congrArg State.matrix (amp_applyState_comp D M ρ)
  rw [hcomp] at hsecond
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at ht
  have hre := congrArg Complex.re hsecond
  unfold variance
  rw [hm]
  simp only [Matrix.mul_assoc] at hre ht ⊢
  linarith

end QuanIncapacity.Shadowing
