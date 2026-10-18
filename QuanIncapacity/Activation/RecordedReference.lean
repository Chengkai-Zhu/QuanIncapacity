import QuanIncapacity.Activation.DephasedErasureInformation

/-! Zero conditional entropy when a classical reference is already recorded
in an orthogonal receiver label. -/

noncomputable section
open QIT
open scoped BigOperators

namespace QuanIncapacity.Activation

variable {r b : Type} [Fintype r] [DecidableEq r] [Fintype b] [DecidableEq b]

theorem copyLabel_conj (f : b → r) (X : CMatrix b) (x y : r) (u v : b) :
    ((copyLabel f).matrix * X * (copyLabel f).matrix.conjTranspose) (x, u) (y, v) =
      if x = f u ∧ y = f v then X u v else 0 := by
  change (∑ k : b, (∑ l : b, (if (x, u) = (f l, l) then (1 : ℂ) else 0) * X l k) *
    star (if (y, v) = (f k, k) then (1 : ℂ) else 0)) = _
  rw [Finset.sum_eq_single v]
  · rw [Finset.sum_eq_single u]
    · by_cases hx : x = f u <;> by_cases hy : y = f v <;> simp [hx, hy]
    · intro l _ hlu
      have hn : (x, u) ≠ (f l, l) := fun h ↦ hlu (congrArg Prod.snd h).symm
      simp [hn]
    · simp
  · intro k _ hkv
    have hn : (y, v) ≠ (f k, k) := fun h ↦ hkv (congrArg Prod.snd h).symm
    simp [hn]
  · simp

theorem coherentInformation_eq_zero_of_recordedReference (ρ : State (r × b)) (f : b → r)
    (hs : ∀ (x y : r) (u v : b), x ≠ f u ∨ y ≠ f v ∨ f u ≠ f v →
      ρ.matrix (x, u) (y, v) = 0) : ρ.coherentInformation = 0 := by
  have he : ρ.matrix = (copyLabel f).matrix * ρ.marginalB.matrix *
      (copyLabel f).matrix.conjTranspose := by
    ext ⟨x, u⟩ ⟨y, v⟩
    rw [copyLabel_conj]
    by_cases hx : x = f u
    · by_cases hy : y = f v
      · rw [if_pos ⟨hx, hy⟩, State.marginalB_matrix]
        change ρ.matrix (x, u) (y, v) = ∑ z, ρ.matrix (z, u) (z, v)
        by_cases hf : f u = f v
        · have hxy : x = y := hx.trans (hf.trans hy.symm)
          rw [Finset.sum_eq_single x]
          · rw [hxy]
          · intro z _ hz
            exact hs z z u v (Or.inl (fun h ↦ hz (h.trans hx.symm)))
          · simp
        · rw [hs x y u v (Or.inr (Or.inr hf))]
          symm
          exact Finset.sum_eq_zero (fun z _ ↦ hs z z u v (Or.inr (Or.inr hf)))
      · rw [if_neg (fun h ↦ hy h.2), hs x y u v (Or.inr (Or.inl hy))]
    · rw [if_neg (fun h ↦ hx h.1), hs x y u v (Or.inl hx)]
  have hh := State.vonNeumann_eq_of_matrix_eq_isometry_conj ρ.marginalB ρ
    (copyLabel f).matrix (copyLabel f).isometry he
  simp [State.coherentInformation_eq, hh]

end QuanIncapacity.Activation

namespace QuanIncapacity.DephasedErasure

variable {r b c : Type} [Fintype r] [DecidableEq r]
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

/-- The dephasing basis records the reference label. The assumption is a
support property of the input, not an entropy inequality. -/
theorem dephasedBranch_coherentInformation_zero (ρ : State (r × (b × c))) (f : c → r)
    (hs : ∀ (x y : r) (u v : b) (i j : c), x ≠ f i ∨ y ≠ f j →
      ρ.matrix (x, (u, i)) (y, (v, j)) = 0) :
    (dephasedBranch ρ).coherentInformation = 0 := by
  haveI : Nonempty r := ρ.nonempty.map Prod.fst
  let g : b × Option c → r := fun u ↦ u.2.elim (Classical.arbitrary r) f
  apply Activation.coherentInformation_eq_zero_of_recordedReference (dephasedBranch ρ) g
  intro x y ⟨u, i⟩ ⟨v, j⟩ hh
  cases i with
  | none => cases j <;> simp [dephasedBranch, success, output_matrix, matrix]
  | some i =>
    cases j with
    | none => simp [dephasedBranch, success, output_matrix, matrix]
    | some j =>
      simp only [g, Option.elim] at hh
      simp only [dephasedBranch, success, output_matrix, matrix,
        Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
        sub_self, sub_zero, zero_add]
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl]
        exact hs x y u v i i (by simpa using hh)
      · simp [hij]

end QuanIncapacity.DephasedErasure
