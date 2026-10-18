import QuanIncapacity.Activation.SingleExcitation
import QuanIncapacity.Framework.ComplementaryTensor

/-! Exact arbitrary-block single-excitation matrix-unit identities. -/

noncomputable section
open QIT
open scoped BigOperators Matrix

namespace QuanIncapacity.Excitation

set_option backward.isDefEq.respectTransparency false

def vacuum : (n : ℕ) → QIT.TensorPower (Fin 2) n
  | 0 => PUnit.unit
  | n + 1 => (0, vacuum n)

theorem vacuum_single_succ (n : ℕ) :
    Matrix.single (vacuum (n + 1)) (vacuum (n + 1)) (1 : ℂ) =
      (Matrix.single (0 : Fin 2) 0 (1 : ℂ)).kronecker
        (Matrix.single (vacuum n) (vacuum n) 1) :=
  single_prod_eq_kronecker_single _ _ _ _

def location : (n : ℕ) → Fin n → QIT.TensorPower (Fin 2) n
  | 0 => Fin.elim0
  | n + 1 => Fin.cases (1, vacuum n) (fun j ↦ (0, location n j))

@[simp] theorem location_zero (n : ℕ) : location (n + 1) 0 = (1, vacuum n) := rfl
@[simp] theorem location_succ (n : ℕ) (i : Fin n) :
    location (n + 1) i.succ = (0, location n i) := rfl

theorem location_ne_vacuum : ∀ n : ℕ, ∀ i : Fin n, location n i ≠ vacuum n
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · intro h
        have hh : (1 : Fin 2) = 0 := congrArg Prod.fst h
        exact (by decide : (1 : Fin 2) ≠ 0) hh
      · intro h
        exact location_ne_vacuum n j (congrArg Prod.snd h)

theorem location_injective : ∀ n : ℕ, Function.Injective (location n)
  | 0 => by intro i; exact Fin.elim0 i
  | n + 1 => by
      intro i j
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases ?_ (fun j' ↦ ?_) j
        · intro _; rfl
        · intro h
          have hh : (1 : Fin 2) = 0 := congrArg Prod.fst h
          exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hh)
      ·
        refine Fin.cases ?_ (fun j' ↦ ?_) j
        · intro h
          have hh : (0 : Fin 2) = 1 := congrArg Prod.fst h
          exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hh)
        · intro h
          exact congrArg Fin.succ (location_injective n (congrArg Prod.snd h))

abbrev power (n : ℕ) := (restrictedQubitChannel.tensorPower n).map

theorem power_kronecker (n : ℕ) (X : CMatrix (Fin 2))
    (Y : CMatrix (QIT.TensorPower (Fin 2) n)) :
    power (n + 1) (X.kronecker Y) = (C_map X).kronecker (power n Y) :=
  MatrixMap.kron_apply_kronecker _ _ X Y

theorem vacuum_fixed : ∀ n : ℕ,
    power n (Matrix.single (vacuum n) (vacuum n) 1) = Matrix.single (vacuum n) (vacuum n) 1
  | 0 => by ext i j; cases i; cases j; rfl
  | n + 1 => by
      erw [vacuum, single_prod_eq_kronecker_single, power_kronecker, C_E00, vacuum_fixed n]

theorem vacuum_location : ∀ n : ℕ, ∀ i : Fin n,
    power n (Matrix.single (vacuum n) (location n i) 1) =
      (1 / 4 : ℂ) • Matrix.single (vacuum n) (location n i) 1
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · erw [vacuum, location_zero, single_prod_eq_kronecker_single, power_kronecker,
          C_E01, vacuum_fixed]
        exact Matrix.smul_kronecker (1 / 4 : ℂ) _ _
      · erw [vacuum, location_succ, single_prod_eq_kronecker_single, power_kronecker,
          C_E00, vacuum_location n j]
        exact Matrix.kronecker_smul (1 / 4 : ℂ) _ _

theorem location_vacuum : ∀ n : ℕ, ∀ i : Fin n,
    power n (Matrix.single (location n i) (vacuum n) 1) =
      (1 / 4 : ℂ) • Matrix.single (location n i) (vacuum n) 1
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · erw [vacuum, location_zero, single_prod_eq_kronecker_single, power_kronecker,
          C_E10, vacuum_fixed]
        exact Matrix.smul_kronecker (1 / 4 : ℂ) _ _
      · erw [vacuum, location_succ, single_prod_eq_kronecker_single, power_kronecker,
          C_E00, location_vacuum n j]
        exact Matrix.kronecker_smul (1 / 4 : ℂ) _ _

theorem diagonal : ∀ n : ℕ, ∀ i : Fin n,
    power n (Matrix.single (location n i) (location n i) 1) =
      (3 / 4 : ℂ) • Matrix.single (vacuum n) (vacuum n) 1 +
      (1 / 4 : ℂ) • Matrix.single (location n i) (location n i) 1
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · erw [location_zero, single_prod_eq_kronecker_single, power_kronecker,
          C_E11, vacuum_fixed, vacuum_single_succ]
        ext x y
        rcases x with ⟨x₁, x₂⟩
        rcases y with ⟨y₁, y₂⟩
        simp [Matrix.kronecker, Matrix.single, Matrix.smul_apply, Matrix.add_apply,
          vacuum, add_mul, mul_ite, ite_mul, mul_assoc]
        split_ifs <;> simp_all
      · erw [location_succ, single_prod_eq_kronecker_single, power_kronecker,
          C_E00, diagonal n j, vacuum_single_succ]
        ext x y
        rcases x with ⟨x₁, x₂⟩
        rcases y with ⟨y₁, y₂⟩
        simp [Matrix.kronecker, Matrix.single, Matrix.smul_apply, Matrix.add_apply,
          vacuum, mul_add, mul_ite, ite_mul, mul_assoc, mul_left_comm]

theorem off_diagonal : ∀ n : ℕ, ∀ i j : Fin n, i ≠ j →
    power n (Matrix.single (location n i) (location n j) 1) =
      (1 / 16 : ℂ) • Matrix.single (location n i) (location n j) 1
  | 0, i, _, _ => Fin.elim0 i
  | n + 1, i, j, hij => by
      revert hij
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases ?_ (fun j' ↦ ?_) j
        · simp
        · intro _
          erw [location_zero, location_succ, single_prod_eq_kronecker_single, power_kronecker,
            C_E10, vacuum_location]
          ext x y
          change ((1 / 4 : ℂ) * _ ) * ((1 / 4 : ℂ) * _) = (1 / 16 : ℂ) * (_ * _)
          ring
      · refine Fin.cases ?_ (fun j' ↦ ?_) j
        · intro _
          erw [location_succ, location_zero, single_prod_eq_kronecker_single, power_kronecker,
            C_E01, location_vacuum]
          ext x y
          change ((1 / 4 : ℂ) * _ ) * ((1 / 4 : ℂ) * _) = (1 / 16 : ℂ) * (_ * _)
          ring
        · intro hij
          erw [location_succ, location_succ, single_prod_eq_kronecker_single, power_kronecker,
            C_E00, off_diagonal n i' j' (by simpa using hij)]
          exact Matrix.kronecker_smul (1 / 16 : ℂ) _ _

def encoder (n : ℕ) : ReferenceIsometry (Fin n) (QIT.TensorPower (Fin 2) n) :=
  ReferenceIsometry.ofInjective (location n) (location_injective n)

end QuanIncapacity.Excitation
