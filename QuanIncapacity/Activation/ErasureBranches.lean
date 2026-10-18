import QuanIncapacity.Activation.InputBranches

/-! Identifying the identity and erased components with their actual input
and marginal states. The extra receiver flag is an isometry. -/

noncomputable section
open QIT
open scoped BigOperators

namespace QuanIncapacity.DephasedErasure

variable {r b c : Type} [Fintype r] [DecidableEq r]
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

def appendNone : ReferenceIsometry b (b × Option c) :=
  ReferenceIsometry.ofInjective (fun x ↦ (x, none)) (fun _ _ h ↦ congrArg Prod.fst h)

def appendSome : ReferenceIsometry (b × c) (b × Option c) :=
  ReferenceIsometry.ofInjective (fun x ↦ (x.1, some x.2))
    (by
      intro ⟨x, i⟩ ⟨y, j⟩ h
      exact Prod.ext (Prod.mk.inj h).1 (Option.some.inj (Prod.mk.inj h).2))

theorem erase_eq_isometry (ρ : State (r × (b × c))) :
    erase ρ = (Activation.dropAuxiliary ρ).conditioningIsometryApply appendNone := by
  apply State.ext
  ext ⟨x, u, i⟩ ⟨y, v, j⟩
  rw [erase, output_matrix]
  change matrix 0 0 (fun k l ↦ ρ.matrix (x, (u, k)) (y, (v, l))) i j =
    ∑ k : b, (∑ l : b, (if (u, i) = (l, none) then (1 : ℂ) else 0) *
      (Activation.dropAuxiliary ρ).matrix (x, l) (y, k)) *
        star (if (v, j) = (k, none) then (1 : ℂ) else 0)
  cases i <;> cases j <;>
    simp [matrix, Prod.mk.injEq, Activation.dropAuxiliary_matrix, Matrix.trace, Matrix.diag]

theorem identityBranch_eq_isometry (ρ : State (r × (b × c))) :
    identityBranch ρ = ρ.conditioningIsometryApply appendSome := by
  apply State.ext
  ext ⟨x, u, i⟩ ⟨y, v, j⟩
  rw [identityBranch, success, output_matrix]
  change matrix 1 1 (fun k l ↦ ρ.matrix (x, (u, k)) (y, (v, l))) i j =
    ∑ k : b × c, (∑ l : b × c, (if (u, i) = (l.1, some l.2) then (1 : ℂ) else 0) *
      ρ.matrix (x, l) (y, k)) * star (if (v, j) = (k.1, some k.2) then (1 : ℂ) else 0)
  cases i <;> cases j <;>
    simp [matrix, Prod.mk.injEq, Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, apply_ite]

theorem erase_coherentInformation (ρ : State (r × (b × c))) :
    (erase ρ).coherentInformation = (Activation.dropAuxiliary ρ).coherentInformation := by
  rw [erase_eq_isometry, Activation.coherentInformation_conditioningIsometry]

theorem identityBranch_coherentInformation (ρ : State (r × (b × c))) :
    (identityBranch ρ).coherentInformation = ρ.coherentInformation := by
  rw [identityBranch_eq_isometry, Activation.coherentInformation_conditioningIsometry]

end QuanIncapacity.DephasedErasure

namespace QuanIncapacity.Activation

variable {a b ι : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype ι] [DecidableEq ι]

theorem signalOutput_erased_coherentInformation (N : Channel a b) (E : Ensemble ι a) :
    (DephasedErasure.erase (signalOutput N E)).coherentInformation =
      -(Ensemble.mapChannel N E).cqState.conditionalEntropy := by
  rw [DephasedErasure.erase_coherentInformation, signalOutput_dropAuxiliary]
  rfl

theorem signalOutput_bound (N : Channel a b) (E : Ensemble ι a) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    q * η * (signalOutput N E).coherentInformation - q * binaryEntropy η -
        (1 - q) * (Ensemble.mapChannel N E).cqState.conditionalEntropy ≤
      (DephasedErasure.output (signalOutput N E) q η hq0 hq1 hη0 hη1).coherentInformation := by
  have hh := DephasedErasure.output_coherentInformation_ge (signalOutput N E) q η hq0 hq1 hη0 hη1
  rw [DephasedErasure.identityBranch_coherentInformation,
    signalOutput_dephased_coherentInformation, signalOutput_erased_coherentInformation] at hh
  simpa only [mul_zero, add_zero, mul_neg, sub_eq_add_neg] using hh

end QuanIncapacity.Activation
