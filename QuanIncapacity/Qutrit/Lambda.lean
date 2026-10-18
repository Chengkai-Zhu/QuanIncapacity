import QIT.Core.Channel
import QuanIncapacity.Util.FinSum

/-!
# The qutrit channel Λ (the x = 1/2 noisy Werner–Holevo channel)

We build the Levi-Civita operators `A_μ` (μ = 0,1,2) and the channel
`Λ(X) = ½X + ¼(Tr(X)·𝟙 − Xᵀ)`, together with its Kraus representation
`K₀ = 𝟙/√2`, `K_{μ+1} = A_μ/2`, and a four-dimensional complementary channel `Λᶜ`.
-/

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

open scoped ComplexOrder MatrixOrder BigOperators
open QIT

namespace QuanIncapacity

/- The Levi-Civita symbol on three natural indices in {0,1,2}, as a complex scalar. -/
def levN (a b c : ℕ) : ℂ :=
  if (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) then 1
  else if (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 2) ∨ (a = 2 ∧ b = 1 ∧ c = 0) then -1
  else 0

/- The skew-symmetric operators `A_μ` with `(A_μ)_{jk} = ε_{μjk}`. -/
def A (μ : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun j k => levN μ.1 j.1 k.1

/- `(√2)² = 2` (over ℂ), the scalar fact used throughout. -/
@[simp]
lemma sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num

/- `(√2)⁻¹ · (√2)⁻¹ = 1/2` (over ℂ), the scalar fact used throughout. -/
@[simp]
lemma sqrt_two_inv_mul_self : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
  calc
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ))⁻¹ := by
      rw [← mul_inv_rev]
    _ = ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ := by rw [sq]
    _ = (2 : ℂ)⁻¹ := by rw [sqrt_two_sq]
    _ = (1 / 2 : ℂ) := by norm_num

/- `((√2)⁻¹)² = 1/2`. -/
@[simp]
lemma sqrt_two_inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
  rw [pow_two]
  exact sqrt_two_inv_mul_self

/- `√2 ≠ 0` (over ℂ). -/
@[simp]
lemma sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : 0 < (2 : ℝ))))

/- `√2 · (√2)⁻¹ = 1` and `(√2)⁻¹ · √2 = 1` (over ℂ). -/
@[simp]
lemma sqrt_two_mul_inv : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ = 1 := by
  exact mul_inv_cancel₀ sqrt_two_ne_zero

@[simp]
lemma sqrt_two_inv_mul : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ) = 1 := by
  exact inv_mul_cancel₀ sqrt_two_ne_zero

lemma sqrt_two_inv_eq_half_sqrt : (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
  calc
    (Real.sqrt 2 : ℂ)⁻¹ * 2 =
        (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) := by
      rw [← pow_two, sqrt_two_sq]
    _ = (Real.sqrt 2 : ℂ) := by rw [← mul_assoc, sqrt_two_inv_mul, one_mul]

@[simp]
lemma sqrt_two_mul_x_mul_inv (x : ℂ) : (Real.sqrt 2 : ℂ) * x * (Real.sqrt 2 : ℂ)⁻¹ = x := by
  rw [mul_assoc, mul_comm x ((Real.sqrt 2 : ℂ)⁻¹), ← mul_assoc, sqrt_two_mul_inv, one_mul]

@[simp]
lemma sqrt_two_inv_mul_x_mul (x : ℂ) : (Real.sqrt 2 : ℂ)⁻¹ * x * (Real.sqrt 2 : ℂ) = x := by
  rw [mul_assoc, mul_comm x (Real.sqrt 2 : ℂ), ← mul_assoc, sqrt_two_inv_mul, one_mul]

/- The index `i ≠ 0` in `Fin 4` corresponds to `μ = i - 1` in `Fin 3`. -/
def fin4ToFin3 {i : Fin 4} (hi : i ≠ (0 : Fin 4)) : Fin 3 :=
  ⟨i.1 - 1, by
    have hlt : i.1 < 4 := i.isLt
    have hne : i.1 ≠ 0 := by
      intro h0
      exact hi (Fin.ext h0)
    omega⟩

/- The Kraus operators of `Λ`: `K₀ = 𝟙/√2`, `K_{μ+1} = A_μ/2`. -/
def K : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ := fun i =>
  if hi : i = (0 : Fin 4) then
    (Real.sqrt 2 : ℂ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℂ)
  else
    (1 / 2 : ℂ) • A (fin4ToFin3 hi)

/- The complementary Kraus operators `E_b` (`b : Fin 3`): `E_b a j = K_a b j`. -/
def Ec (b : Fin 3) : Matrix (Fin 4) (Fin 3) ℂ := fun a j => K a b j

/- `Σ_μ A_μ† A_μ = 2·𝟙₃`. -/
lemma sum_A_dagger_A : ∑ μ : Fin 3, (A μ).conjTranspose * A μ = 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A, levN, Matrix.mul_apply] <;> norm_num

/- `Σ_μ A_μ X A_μ† = Tr(X)·𝟙 − Xᵀ` for any `X`. -/
lemma sum_A_mul_A_dagger (X : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ μ : Fin 3, A μ * X * (A μ).conjTranspose =
      (Matrix.trace X : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - X.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, levN, Matrix.mul_apply, Matrix.trace] <;> ring

/- `Σ_a K_a† K_a = 𝟙₃`. -/
lemma sum_K_dagger_K : ∑ a : Fin 4, (K a).conjTranspose * K a = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, A, levN, fin4ToFin3, Matrix.mul_apply] <;> norm_num [starRingEnd]

/- The linear map `Λ` in closed form. -/
def Λ_map : MatrixMap (Fin 3) (Fin 3) where
  toFun X := (1 / 2 : ℂ) • X + (1 / 4 : ℂ) • ((Matrix.trace X : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - X.transpose)
  map_add' X Y := by
    ext i j
    simp [Matrix.trace_add, Matrix.transpose_add, Matrix.add_apply, Matrix.smul_apply]
    ring
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul, Matrix.transpose_smul, Matrix.smul_apply]
    ring

/- `Λ` equals its Kraus form. -/
lemma Λ_map_eq_ofKraus : Λ_map = MatrixMap.ofKraus (K : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) := by
  ext X i j
  fin_cases i <;> fin_cases j <;>
    simp [Λ_map, MatrixMap.ofKraus, K, A, levN, fin4ToFin3, Matrix.mul_apply, Matrix.trace] <;>
    norm_num [starRingEnd] <;>
    ring_nf <;>
    simp <;>
    ring

/- The qutrit channel `Λ`, a CPTP map. -/
def Λ : Channel (Fin 3) (Fin 3) where
  map := Λ_map
  completelyPositive := by
    rw [Λ_map_eq_ofKraus]
    exact MatrixMap.ofKraus_completelyPositive (K : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ)
  tracePreserving := by
    rw [Λ_map_eq_ofKraus]
    exact MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one
      (K : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) (by simpa [MatrixMap.krausAdjoint] using sum_K_dagger_K)
  mapsPositive := by
    intro X hX
    rw [Λ_map_eq_ofKraus]
    exact MatrixMap.ofKraus_mapsPositive (K : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ) X hX

/- `Λ` fixes the identity: `Λ(𝟙) = 𝟙`. -/
lemma Λ_one : Λ_map (1 : Matrix (Fin 3) (Fin 3) ℂ) = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Λ_map, Matrix.trace] <;> norm_num

/- The complementary channel in Gram form: `⟨a|Λᶜ(X)|b⟩ = Tr(K_a X K_b†)`. -/
def Λc_map : MatrixMap (Fin 3) (Fin 4) where
  toFun X := fun a b => ((K a) * X * (K b).conjTranspose).trace
  map_add' X Y := by
    ext a b
    change (K a * (X + Y) * (K b).conjTranspose).trace =
      (K a * X * (K b).conjTranspose).trace + (K a * Y * (K b).conjTranspose).trace
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' c X := by
    ext a b
    change (K a * (c • X) * (K b).conjTranspose).trace =
      c * (K a * X * (K b).conjTranspose).trace
    simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul]

/- `Λᶜ` equals its Kraus form (indexed by the output `b : Fin 3`). -/
lemma Λc_map_eq_ofKraus : Λc_map = MatrixMap.ofKraus (Ec : Fin 3 → Matrix (Fin 4) (Fin 3) ℂ) := by
  ext X a a'
  change ((K a) * X * (K a').conjTranspose).trace =
    (∑ t : Fin 3, Ec t * X * (Ec t).conjTranspose) a a'
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Ec]

/- `Λᶜ` is completely positive. -/
lemma Λc_map_completelyPositive : MatrixMap.IsCompletelyPositive Λc_map := by
  rw [Λc_map_eq_ofKraus]
  exact MatrixMap.ofKraus_completelyPositive (Ec : Fin 3 → Matrix (Fin 4) (Fin 3) ℂ)

/- `Λᶜ` is trace preserving. -/
lemma Λc_map_tracePreserving : MatrixMap.IsTracePreserving Λc_map := by
  intro X
  change (∑ a : Fin 4, (K a * X * (K a).conjTranspose).trace) = X.trace
  rw [← Matrix.trace_sum]
  change (MatrixMap.ofKraus K X).trace = X.trace
  rw [← Λ_map_eq_ofKraus]
  exact Λ.tracePreserving X

/- The complementary channel `Λᶜ`. -/
def Λc : Channel (Fin 3) (Fin 4) where
  map := Λc_map
  completelyPositive := Λc_map_completelyPositive
  tracePreserving := Λc_map_tracePreserving
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive Λc_map Λc_map_completelyPositive

/- `Λᶜ(𝟙) = diag(3/2, 1/2, 1/2, 1/2)`. -/
lemma Λc_one : Λc_map (1 : Matrix (Fin 3) (Fin 3) ℂ) =
    (fun a b : Fin 4 => if a = b then (if a = 0 then (3/2 : ℂ) else (1/2 : ℂ)) else 0) := by
  ext a b
  change (K a * 1 * (K b).conjTranspose).trace = _
  fin_cases a <;> fin_cases b <;>
    simp [K, A, levN, fin4ToFin3, Matrix.mul_apply, Matrix.trace] <;> norm_num [starRingEnd]

end QuanIncapacity
