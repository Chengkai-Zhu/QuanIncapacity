import QuanIncapacity.Framework.PPTChannel
import QIT.Coding.Quantum.Basic

/-! A PPT state has squared fidelity at most `1/K` with a maximally
entangled target of local dimension `K`. -/

noncomputable section
open QIT
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace QuanIncapacity.PPT

variable {a b : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

def exchange (p : a ≃ b) : a × b ≃ a × b where
  toFun x := (p.symm x.2, p x.1)
  invFun x := (p.symm x.2, p x.1)
  left_inv x := by simp
  right_inv x := by simp

def swap (p : a ≃ b) : CMatrix (a × b) :=
  (ReferenceIsometry.ofEquiv (exchange p)).matrix

theorem swap_hermitian (p : a ≃ b) : (swap p).IsHermitian := by
  ext x y
  have he : y = exchange p x ↔ x = exchange p y := by
    constructor <;> intro h
    · simpa [exchange] using (congrArg (exchange p) h).symm
    · simpa [exchange] using (congrArg (exchange p) h).symm
  change star (if y = exchange p x then (1 : ℂ) else 0) =
    if x = exchange p y then 1 else 0
  simp [he]

theorem swap_square (p : a ≃ b) : swap p * swap p = 1 := by
  have h := (ReferenceIsometry.ofEquiv (exchange p)).isometry
  change (swap p).conjTranspose * swap p = 1 at h
  rw [(swap_hermitian p).eq] at h
  exact h

theorem one_sub_swap_pos (p : a ≃ b) : (1 - swap p).PosSemidef := by
  have hgram : (1 - swap p).conjTranspose * (1 - swap p) =
      (2 : ℝ) • (1 - swap p) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (swap_hermitian p).eq,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, swap_square]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    norm_num
    ring
  have he : 1 - swap p = (1 / 2 : ℝ) •
      ((1 - swap p).conjTranspose * (1 - swap p)) := by
    rw [hgram, smul_smul]
    norm_num
  rw [he]
  exact (Matrix.posSemidef_conjTranspose_mul_self (1 - swap p)).smul (by norm_num)

theorem trace_partialTranspose_pair (X Y : CMatrix (a × b)) :
    (partialTransposeB X * partialTransposeB Y).trace = (X * Y).trace := by
  let v : ((a × b) × (a × b)) ≃ ((a × b) × (a × b)) :=
    { toFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
      invFun x := ((x.1.1, x.2.2), (x.2.1, x.1.2))
      left_inv _ := rfl
      right_inv _ := rfl }
  have ht (A B : CMatrix (a × b)) : (A * B).trace =
      ∑ ij : (a × b) × (a × b), A ij.1 ij.2 * B ij.2 ij.1 := by
    simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [ht, ht]
  exact Equiv.sum_comp v (fun ij ↦ X ij.1 ij.2 * Y ij.2 ij.1)

theorem trace_partialTranspose (X : CMatrix (a × b)) :
    (partialTransposeB X).trace = X.trace := by
  rfl

theorem maximallyEntangled_partialTranspose [Nonempty a] (p : a ≃ b) :
    partialTransposeB (State.maximallyEntangled p).matrix =
      ((Fintype.card a : ℝ)⁻¹) • swap p := by
  have hk : 0 ≤ (Fintype.card a : ℝ) := Nat.cast_nonneg _
  have hsquare : (Real.sqrt (Fintype.card a : ℝ) : ℂ) ^ 2 = (Fintype.card a : ℂ) := by
    exact_mod_cast Real.sq_sqrt hk
  have hnorm : (Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹ = (Fintype.card a : ℂ)⁻¹ := by
    rw [← mul_inv_rev, ← pow_two, hsquare]
  ext x y
  have he : x = exchange p y ↔ p x.1 = y.2 ∧ p y.1 = x.2 := by
    constructor
    · intro h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      exact ⟨by simpa [exchange] using congrArg p h₁, by simpa [exchange] using h₂.symm⟩
    · rintro ⟨h₁, h₂⟩
      apply Prod.ext
      · simpa [exchange] using congrArg p.symm h₁
      · exact h₂.symm
  change (PureVector.maximallyEntangled p).state.matrix (x.1, y.2) (y.1, x.2) = _
  simp only [PureVector.state_matrix_apply, PureVector.maximallyEntangled_amp,
    Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [show swap p x y = (if x = exchange p y then 1 else 0) from rfl]
  by_cases h₁ : p x.1 = y.2 <;> by_cases h₂ : p y.1 = x.2 <;>
    simp [h₁, h₂, he, Complex.star_def, Complex.conj_ofReal, hnorm]

theorem fidelity_le_inv_card [Nonempty a] (ρ : State (a × b)) (hρ : QIT.IsPPT ρ)
    (p : a ≃ b) : ρ.squaredFidelity (State.maximallyEntangled p) ≤ (Fintype.card a : ℝ)⁻¹ := by
  let s := (Fintype.card a : ℝ)⁻¹
  have hs : 0 ≤ s := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hp : (s • (1 : CMatrix (a × b)) -
      partialTransposeB (State.maximallyEntangled p).matrix).PosSemidef := by
    rw [maximallyEntangled_partialTranspose]
    change (s • (1 : CMatrix (a × b)) - s • swap p).PosSemidef
    rw [← smul_sub]
    exact (one_sub_swap_pos p).smul hs
  have ht := cMatrix_trace_mul_posSemidef_re_nonneg hρ hp
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, trace_partialTranspose, ρ.trace_eq_one,
    trace_partialTranspose_pair] at ht
  change ρ.squaredFidelity (PureVector.maximallyEntangled p).state ≤ _
  rw [State.squaredFidelity_pure_right_eq_trace ρ (PureVector.maximallyEntangled p)]
  change _ ≤ s
  simpa only [State.maximallyEntangled, Complex.real_smul, smul_eq_mul, mul_one,
    Complex.ofReal_re] using sub_nonneg.mp ht

end QuanIncapacity.PPT
