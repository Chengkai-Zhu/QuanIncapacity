import Mathlib.Tactic

/-!
# Finite-sum helpers
-/

noncomputable section

namespace QuanIncapacity

open scoped BigOperators

@[simp]
lemma sum_univ_three {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) :
    ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [add_assoc]

@[simp]
lemma sum_univ_four {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [add_assoc]

end QuanIncapacity
