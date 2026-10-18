import QuanIncapacity.Activation.EntropyBounds
import QIT.Information.Renyi.AlphaEntropyContinuity

/-! An already distinguishable receiver flag does not cost entropy.
The support conditions are matrix statements, so this also handles coherences
within each flagged subspace and branches of weight zero. -/

noncomputable section
open QIT
open scoped BigOperators

namespace QuanIncapacity.Activation

variable {r b ι : Type} [Fintype r] [DecidableEq r]
variable [Fintype b] [DecidableEq b] [Fintype ι] [DecidableEq ι]

def copyLabel (f : b → ι) : ReferenceIsometry b (ι × b) :=
  ReferenceIsometry.ofInjective (fun x ↦ (f x, x))
    (fun _ _ h ↦ congrArg Prod.snd h)

theorem copyLabel_matrix (f : b → ι) (ρ : State (r × b))
    (x y : r) (i j : ι) (u v : b) :
    (ρ.conditioningIsometryApply (copyLabel f)).matrix (x, (i, u)) (y, (j, v)) =
      if i = f u ∧ j = f v then ρ.matrix (x, u) (y, v) else 0 := by
  change (∑ k : b, (∑ l : b, (if (i, u) = (f l, l) then (1 : ℂ) else 0) *
    ρ.matrix (x, l) (y, k)) * star (if (j, v) = (f k, k) then (1 : ℂ) else 0)) = _
  rw [Finset.sum_eq_single v]
  · rw [Finset.sum_eq_single u]
    · by_cases hi : i = f u <;> by_cases hj : j = f v <;> simp [hi, hj]
    · intro l _ hlu
      have hn : (i, u) ≠ (f l, l) := fun h ↦ hlu (congrArg Prod.snd h).symm
      simp [hn]
    · simp
  · intro k _ hkv
    have hn : (j, v) ≠ (f k, k) := fun h ↦ hkv (congrArg Prod.snd h).symm
    simp [hn]
  · simp

theorem receiverFlaggedState_matrix (E : Ensemble ι (r × b))
    (x y : r) (i j : ι) (u v : b) :
    (receiverFlaggedState E).matrix (x, (i, u)) (y, (j, v)) =
      ∑ k, if i = k ∧ j = k then
        (E.probs k : ℂ) * (E.states k).matrix (x, u) (y, v) else 0 := by
  simp [receiverFlaggedState, receiverFlagEquiv, State.reindex,
    Ensemble.cqState_matrix, Matrix.sum_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.smul_apply,
    ite_and, ite_mul, eq_comm, NNReal.smul_def, Complex.real_smul]

theorem copyLabel_average_eq_flagged (E : Ensemble ι (r × b)) (f : b → ι)
    (hs : ∀ i (x y : r) (u v : b), f u ≠ i ∨ f v ≠ i →
      (E.states i).matrix (x, u) (y, v) = 0) :
    E.averageState.conditioningIsometryApply (copyLabel f) = receiverFlaggedState E := by
  apply State.ext
  ext ⟨x, i, u⟩ ⟨y, j, v⟩
  rw [copyLabel_matrix, receiverFlaggedState_matrix]
  simp only [Ensemble.averageState_matrix, Matrix.sum_apply, Matrix.smul_apply]
  have hh (P : Prop) [Decidable P] (g : ι → ℂ) :
      (if P then ∑ k, g k else 0) = ∑ k, if P then g k else 0 := by
    by_cases h : P <;> simp [h]
  rw [hh]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hu : f u = k <;> by_cases hv : f v = k
  · simp [hu, hv, NNReal.smul_def, Complex.real_smul]
  · simp [hs k x y u v (Or.inr hv)]
  · simp [hs k x y u v (Or.inl hu)]
  · simp [hs k x y u v (Or.inl hu)]

theorem coherentInformation_conditioningIsometry (ρ : State (r × b))
    {c : Type} [Fintype c] [DecidableEq c] (V : ReferenceIsometry b c) :
    (ρ.conditioningIsometryApply V).coherentInformation = ρ.coherentInformation := by
  simp only [State.coherentInformation, State.conditionalEntropy_conditioningIsometryApply]

/-- Exact coherent-information average for branches distinguishable at the receiver. -/
theorem coherentInformation_average_orthogonal (E : Ensemble ι (r × b)) (f : b → ι)
    (hs : ∀ i (x y : r) (u v : b), f u ≠ i ∨ f v ≠ i →
      (E.states i).matrix (x, u) (y, v) = 0) :
    E.averageState.coherentInformation =
      ∑ i, (E.probs i : ℝ) * (E.states i).coherentInformation := by
  rw [← coherentInformation_conditioningIsometry E.averageState (copyLabel f),
    copyLabel_average_eq_flagged E f hs, receiverFlaggedState_coherentInformation]

end QuanIncapacity.Activation
