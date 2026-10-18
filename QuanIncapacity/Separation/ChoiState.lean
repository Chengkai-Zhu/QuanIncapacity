import QuanIncapacity.Qutrit.Lambda

/-!
# The explicit Choi matrix and its NPT certificate

The Choi state `ω^Λ = (id ⊗ Λ)(Φ₃) = ½Φ₃ + ⅙P⁻` of the qutrit channel `Λ`, its
partial transpose on the first system, and the NPT witness. Here
* `Φ₃ ((a,b),(a',b')) = (1/3)·[a=b]·[a'=b']` is the normalized maximally
  entangled state;
* `F ((a,b),(a',b')) = [a=b']·[b=a']` is the swap operator;
* `P⁻ = (𝟙 − F)/2` is the antisymmetric projector.

The partial transpose is `(ω^Λ)^{T_A} = (1/12)(𝟙 + 2F − 3Φ₃)`, with spectrum
`{¼×5, 0, −1/12×3}`. The Schmidt-rank-two vector `ψ⁻₀₁ = (|01⟩ − |10⟩)/√2` gives
`⟨ψ⁻₀₁ | (ω^Λ)^{T_A} | ψ⁻₀₁⟩ = −1/12`. This file proves NPT. The paper's
operational distillability inference uses the Schmidt-rank-two criterion and is
not formalized here. `ChoiBridge` connects this matrix to the actual channel.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT

namespace QuanIncapacity

/- The bipartite qutrit system `A : B = Fin 3 ⊗ Fin 3`. -/
abbrev Sys33 := Prod (Fin 3) (Fin 3)

/- The maximally entangled state `Φ₃ = (1/3) Σᵢⱼ |i⟩⟨j| ⊗ |i⟩⟨j|`. -/
def Phi3 : Matrix Sys33 Sys33 ℂ :=
  fun ab a'b' => (1 / 3 : ℂ) * (if ab.1 = ab.2 then 1 else 0) * (if a'b'.1 = a'b'.2 then 1 else 0)

/- The swap operator `F = Σᵢⱼ |i⟩⟨j| ⊗ |j⟩⟨i|`. -/
def swap3 : Matrix Sys33 Sys33 ℂ :=
  fun ab a'b' => (if ab.1 = a'b'.2 then 1 else 0 : ℂ) * (if ab.2 = a'b'.1 then 1 else 0)

/- The antisymmetric projector `P⁻ = (𝟙 − F)/2`. -/
def Pminus : Matrix Sys33 Sys33 ℂ :=
  (1 / 2 : ℂ) • ((1 : Matrix Sys33 Sys33 ℂ) - swap3)

/- The Choi state `ω^Λ = ½Φ₃ + ⅙P⁻`. -/
def omega : Matrix Sys33 Sys33 ℂ :=
  (1 / 2 : ℂ) • Phi3 + (1 / 6 : ℂ) • Pminus

/- Partial transpose on the first (A) system. -/
def ptA (M : Matrix Sys33 Sys33 ℂ) : Matrix Sys33 Sys33 ℂ :=
  fun ab a'b' => M (a'b'.1, ab.2) (ab.1, a'b'.2)

/- `Φ₃^{T_A} = F/3`. -/
lemma ptA_Phi3 : ptA Phi3 = (1 / 3 : ℂ) • swap3 := by
  ext ab a'b'
  rcases ab with ⟨a, b⟩
  rcases a'b' with ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [ptA, Phi3, swap3, Matrix.smul_apply] <;> norm_num

/- `F^{T_A} = 3Φ₃`. -/
lemma ptA_swap3 : ptA swap3 = (3 : ℂ) • Phi3 := by
  ext ab a'b'
  rcases ab with ⟨a, b⟩
  rcases a'b' with ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [ptA, Phi3, swap3, Matrix.smul_apply] <;> norm_num

/- `(ω^Λ)^{T_A} = (1/12)(𝟙 + 2F − 3Φ₃)`. -/
lemma ptA_omega : ptA omega =
    (1 / 12 : ℂ) • (1 : Matrix Sys33 Sys33 ℂ) + (1 / 6 : ℂ) • swap3 - (1 / 4 : ℂ) • Phi3 := by
  ext ab a'b'
  rcases ab with ⟨a, b⟩
  rcases a'b' with ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [ptA, omega, Pminus, Phi3, swap3, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply] <;> norm_num

/- The NPT witness value: `2·⟨ψ⁻₀₁ | (ω^Λ)^{T_A} | ψ⁻₀₁⟩ = −1/6` for the
  (unnormalized) vector `ψ⁻₀₁ = |01⟩ − |10⟩`, i.e.
  `M(0,1)(0,1) − M(0,1)(1,0) − M(1,0)(0,1) + M(1,0)(1,0) = −1/6`. -/
lemma omega_NPT_witness :
    (ptA omega) (0, 1) (0, 1) - (ptA omega) (0, 1) (1, 0)
      - (ptA omega) (1, 0) (0, 1) + (ptA omega) (1, 0) (1, 0)
      = (-1 / 6 : ℂ) := by
  simp [ptA, omega, Pminus, Phi3, swap3, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.one_apply]
  norm_num

/- The embedding of the 2-dimensional witness subspace `span{|01⟩, |10⟩}` into
  `Fin 3 ⊗ Fin 3`. -/
def emb2 : Fin 2 → Sys33 := fun i => if i = 0 then (0, 1) else (1, 0)

/- The (unnormalized) witness vector `|01⟩ − |10⟩`, restricted to the 2×2
  principal submatrix on `{|01⟩, |10⟩}`. -/
def witness2 : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1

/- `⟨ψ⁻₀₁ | (ω^Λ)^{T_A} | ψ⁻₀₁⟩ = −1/6 < 0` (the unnormalized vector gives −1/6,
  the normalized one −1/12), computed on the 2×2 principal submatrix. -/
lemma witness_expectation :
    star witness2 ⬝ᵥ ((ptA omega).submatrix emb2 emb2 *ᵥ witness2) = (-1 / 6 : ℂ) := by
  simp [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, witness2, emb2,
    ptA, omega, Pminus, Phi3, swap3, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.one_apply]
  norm_num

/- The Choi state of `Λ` is NPT: its partial transpose is not positive
  semidefinite, witnessed by the vector `|01⟩ − |10⟩`. -/
lemma omega_not_PPT : ¬ Matrix.PosSemidef (ptA omega) := by
  intro h
  have hsub := Matrix.PosSemidef.submatrix h emb2
  have hnonneg := Matrix.PosSemidef.dotProduct_mulVec_nonneg hsub witness2
  have hcomp : star witness2 ⬝ᵥ ((ptA omega).submatrix emb2 emb2 *ᵥ witness2) = (-1 / 6 : ℂ) :=
    witness_expectation
  rw [hcomp] at hnonneg
  have hre := (Complex.nonneg_iff.mp hnonneg).1
  norm_num at hre

end QuanIncapacity
