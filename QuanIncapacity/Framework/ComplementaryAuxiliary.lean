import QuanIncapacity.Framework.ComplementaryTensor
import QuanIncapacity.Framework.ComplementaryInformation

/-! Transmitting an auxiliary register gives the complementary channel that
discards that register. Both channels are certified by one explicit isometry. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open QIT
open scoped BigOperators Matrix

namespace QuanIncapacity

variable {a b c e r : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
variable [Fintype e] [DecidableEq e] [Fintype r] [DecidableEq r]

namespace Stinespring

def auxiliaryRegroup (b e c : Type) : (b × e) × c ≃ (b × c) × e where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def keepAuxiliary (V : ReferenceIsometry a (b × e)) :
    ReferenceIsometry (a × c) ((b × c) × e) :=
  reindexOutput (V.prod (ReferenceIsometry.ofEquiv (Equiv.refl c))) (auxiliaryRegroup b e c)

theorem keepAuxiliary_lift (V : ReferenceIsometry a (b × e)) (X : CMatrix a) (Y : CMatrix c) :
    (keepAuxiliary V).matrix * X.kronecker Y * (keepAuxiliary V).matrixᴴ =
      ((V.matrix * X * V.matrixᴴ).kronecker Y).submatrix
        (auxiliaryRegroup b e c).symm (auxiliaryRegroup b e c).symm := by
  rw [keepAuxiliary, reindexOutput_lift]
  congr 1
  have hi : (ReferenceIsometry.ofEquiv (Equiv.refl c)).matrix = (1 : CMatrix c) := by
    ext i j
    by_cases h : i = j <;> simp [ReferenceIsometry.ofEquiv, Matrix.one_apply, h]
  change (V.matrix.kronecker (ReferenceIsometry.ofEquiv (Equiv.refl c)).matrix) * _ *
    (V.matrix.kronecker (ReferenceIsometry.ofEquiv (Equiv.refl c)).matrix)ᴴ = _
  rw [hi]
  rw [show (V.matrix.kronecker (1 : CMatrix c))ᴴ = V.matrixᴴ.kronecker (1 : CMatrix c) from
    by
      ext ⟨i, k⟩ ⟨j, l⟩
      change star (V.matrix j i * (if l = k then (1 : ℂ) else 0)) =
        star (V.matrix j i) * (if k = l then (1 : ℂ) else 0)
      by_cases h : k = l <;> simp [h, eq_comm]]
  rw [show V.matrix.kronecker 1 * X.kronecker Y =
    (V.matrix * X).kronecker Y by simpa using (Matrix.mul_kronecker_mul V.matrix X (1 : CMatrix c) Y).symm]
  simpa using (Matrix.mul_kronecker_mul (V.matrix * X) V.matrixᴴ Y (1 : CMatrix c)).symm

theorem keepAuxiliary_output (V : ReferenceIsometry a (b × e)) :
    (keepAuxiliary (c := c) V).outputChannel = V.outputChannel.prod (Channel.idChannel c) := by
  apply channel_eq_of_map_eq
  apply matrixMap_eq_of_kronecker
  intro X Y
  rw [ReferenceIsometry.outputChannel_map, keepAuxiliary_lift]
  rw [Channel.prod_map_kronecker, idChannel_map_eq, LinearMap.id_apply]
  rw [ReferenceIsometry.outputChannel_map]
  change partialTraceB (a := b × c) (b := e) _ =
    (partialTraceB (a := b) (b := e) (V.matrix * X * V.matrixᴴ)).kronecker Y
  ext i j
  simp [partialTraceB, auxiliaryRegroup, Matrix.kronecker, ← Finset.sum_mul]

theorem keepAuxiliary_complement (V : ReferenceIsometry a (b × e)) :
    (keepAuxiliary (c := c) V).complementaryChannel =
      V.complementaryChannel.comp (Channel.traceOutRight a c) := by
  apply channel_eq_of_map_eq
  apply matrixMap_eq_of_kronecker
  intro X Y
  rw [ReferenceIsometry.complementaryChannel_map, keepAuxiliary_lift]
  change partialTraceA _ = V.complementaryChannel.map (partialTraceB (X.kronecker Y))
  rw [partialTraceB_kronecker]
  change _ = V.complementaryChannel.map (Y.trace • X)
  rw [map_smul, ReferenceIsometry.complementaryChannel_map]
  ext i j
  simp [partialTraceA, auxiliaryRegroup, Matrix.kronecker, Fintype.sum_prod_type,
    Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Stinespring

theorem ComplementaryChannels.keepAuxiliary {N : Channel a b} {M : Channel a e}
    (hc : ComplementaryChannels N M) :
    ComplementaryChannels (N.prod (Channel.idChannel c)) (M.comp (Channel.traceOutRight a c)) := by
  obtain ⟨V, rfl, rfl⟩ := hc
  exact ⟨Stinespring.keepAuxiliary V, Stinespring.keepAuxiliary_output V,
    Stinespring.keepAuxiliary_complement V⟩

theorem ComplementaryChannels.coherentInformationFor_eq_complement_conditionalEntropy
    {N : Channel a b} {M : Channel a e} (hc : ComplementaryChannels N M)
    (ψ : PureVector (r × a)) :
    N.coherentInformationFor ψ =
      (((Channel.idChannel r).prod M).applyState ψ.state).conditionalEntropy := by
  obtain ⟨V, rfl, rfl⟩ := hc
  rw [Channel.coherentInformationFor, State.coherentInformation_eq, State.conditionalEntropy_eq,
    Stinespring.receiver_reference_entropy, Stinespring.environment_reference_entropy,
    State.marginalB_applyState_prod, State.marginalB_applyState_prod]

end QuanIncapacity
