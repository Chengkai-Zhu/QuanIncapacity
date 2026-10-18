import QuanIncapacity.Qutrit.Lambda

/-!
# The shadow map 𝒥 for the qutrit channel

`𝒥 : Lin(ℂ³) → Lin(ℂ⁴)` is a complex-linear, adjoint-preserving (but not positive)
map witnessing complete observable shadowing of `Λ` by `Λᶜ`: it satisfies the lift
identity `(Λᶜ)† ∘ 𝒥 = Λ`.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT

namespace QuanIncapacity

open QuanIncapacity

/- The skew vector `a(Y)_μ = Σ_{jk} ε_{μjk} Y_{jk} = (Y₁₂−Y₂₁, Y₂₀−Y₀₂, Y₀₁−Y₁₀)`. -/
def avec (Y : Matrix (Fin 3) (Fin 3) ℂ) (μ : Fin 3) : ℂ :=
  (A μ * Y.transpose).trace

/- The index embedding `Fin 3 → Fin 4`, `μ ↦ μ + 1`. -/
def fin3ToFin4 (μ : Fin 3) : Fin 4 := ⟨μ.1 + 1, by omega⟩

@[simp] lemma fin3ToFin4_zero : fin3ToFin4 (0 : Fin 3) = (1 : Fin 4) := by ext; norm_num [fin3ToFin4]
@[simp] lemma fin3ToFin4_one : fin3ToFin4 (1 : Fin 3) = (2 : Fin 4) := by ext; norm_num [fin3ToFin4]
@[simp] lemma fin3ToFin4_two : fin3ToFin4 (2 : Fin 3) = (3 : Fin 4) := by ext; norm_num [fin3ToFin4]

@[simp] lemma fin4ToFin3_one (hi : (1 : Fin 4) ≠ (0 : Fin 4)) : fin4ToFin3 hi = (0 : Fin 3) := by ext; norm_num [fin4ToFin3]
@[simp] lemma fin4ToFin3_two (hi : (2 : Fin 4) ≠ (0 : Fin 4)) : fin4ToFin3 hi = (1 : Fin 3) := by ext; norm_num [fin4ToFin3]
@[simp] lemma fin4ToFin3_three (hi : (3 : Fin 4) ≠ (0 : Fin 4)) : fin4ToFin3 hi = (2 : Fin 3) := by ext; norm_num [fin4ToFin3]

/- The shadow map `𝒥`. -/
def shadowEntries (Y : CMatrix (Fin 3)) : CMatrix (Fin 4) := fun a b =>
    if ha : a = (0 : Fin 4) then
      if hb : b = (0 : Fin 4) then
        (1 / 3 : ℂ) * (Matrix.trace Y : ℂ)
      else
        (Real.sqrt 2 : ℂ) / 3 * avec Y (fin4ToFin3 hb)
    else
      if hb : b = (0 : Fin 4) then
        -(Real.sqrt 2 : ℂ) / 3 * avec Y (fin4ToFin3 ha)
      else
        (1 / 3 : ℂ) * (2 * (Matrix.trace Y : ℂ) * (if (fin4ToFin3 ha) = (fin4ToFin3 hb) then (1 : ℂ) else 0)
          - Y (fin4ToFin3 ha) (fin4ToFin3 hb) - 2 * Y (fin4ToFin3 hb) (fin4ToFin3 ha))
def 𝒥_map : MatrixMap (Fin 3) (Fin 4) where
  toFun := shadowEntries
  map_add' Y Z := by
    ext a b
    change shadowEntries (Y + Z) a b = shadowEntries Y a b + shadowEntries Z a b
    fin_cases a <;> fin_cases b <;>
      simp [shadowEntries, avec, A, levN, fin4ToFin3, fin3ToFin4, Matrix.trace_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
    all_goals ring
  map_smul' c Y := by
    ext a b
    change shadowEntries (c • Y) a b = c * shadowEntries Y a b
    fin_cases a <;> fin_cases b <;>
      simp [shadowEntries, avec, A, levN, fin4ToFin3, fin3ToFin4, Matrix.trace_smul, Matrix.transpose_smul, mul_ite, add_ite]
    all_goals ring

@[simp] lemma 𝒥_map_apply (Y : CMatrix (Fin 3)) (a b : Fin 4) :
    𝒥_map Y a b = shadowEntries Y a b := rfl

/- Lift identity: `(Λᶜ)† ∘ 𝒥 = Λ` (Heisenberg picture). -/
lemma 𝒥_lift (Y : Matrix (Fin 3) (Fin 3) ℂ) :
    MatrixMap.krausAdjoint (Ec : Fin 3 → Matrix (Fin 4) (Fin 3) ℂ) (𝒥_map Y) = Λ_map Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixMap.krausAdjoint, Ec, K, A, levN, fin4ToFin3, fin3ToFin4, shadowEntries, avec,
      Λ_map, Matrix.mul_apply, Matrix.trace, Matrix.transpose, sqrt_two_inv_eq_half_sqrt]
  all_goals
    change Fin 3 → Fin 3 → ℂ at Y
    norm_num [map_ofNat]
    ring_nf
    try simp only [sqrt_two_sq]
    ring

/- `avec (Y†) μ = -star (avec Y μ)`: the skew vector changes sign under the adjoint
  (since `A_μ` is real skew-symmetric, `(A_μ)† = -A_μ`). -/
@[simp] lemma avec_conjTranspose (Y : Matrix (Fin 3) (Fin 3) ℂ) (μ : Fin 3) :
    avec (Y.conjTranspose) μ = -star (avec Y μ) := by
  fin_cases μ <;>
    simp [avec, A, levN, Matrix.trace, Matrix.transpose, Matrix.conjTranspose, Matrix.mul_apply]

/- Adjoint preservation: `𝒥(Y†) = 𝒥(Y)†`. -/
lemma 𝒥_adjoint_preserving (Y : Matrix (Fin 3) (Fin 3) ℂ) :
    𝒥_map (Y.conjTranspose) = (𝒥_map Y).conjTranspose := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [shadowEntries, Matrix.trace_conjTranspose, Matrix.conjTranspose_apply] <;>
    ring

lemma 𝒥_E00_diag_neg : (𝒥_map (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))) 1 1 = (-1 / 3 : ℂ) := by
  have h1 : (1 : Fin 4) ≠ (0 : Fin 4) := by decide
  simp [shadowEntries, h1, fin4ToFin3_one, Matrix.trace, Matrix.single]
  norm_num

lemma 𝒥_not_positive :
    ¬ (𝒥_map (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ))).PosSemidef := by
  intro h
  let e : Fin 4 → ℂ := fun i => if i = (1 : Fin 4) then 1 else 0
  have hnonneg := h.dotProduct_mulVec_nonneg e
  have hcomp : star e ⬝ᵥ (𝒥_map (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ)) *ᵥ e)
      = (-1 / 3 : ℂ) := by
    have h1 : (1 : Fin 4) ≠ (0 : Fin 4) := by decide
    simp [e, dotProduct, Matrix.mulVec, shadowEntries, h1, fin4ToFin3_one, Matrix.trace, Matrix.single]
    norm_num
  rw [hcomp] at hnonneg
  have hre := (Complex.nonneg_iff.mp hnonneg).1
  norm_num at hre

end QuanIncapacity
