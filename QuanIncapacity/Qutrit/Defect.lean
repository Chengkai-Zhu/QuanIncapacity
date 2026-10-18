import QuanIncapacity.Qutrit.ShadowMap

/-!
# The completely positive outer defect

The outer defect `Δ(τ) = L_{Λ(τ)} − 𝒥†∘L_{Λᶜ(τ)}∘𝒥` is completely positive, with
the exact Kraus factorization `Δ(τ) = (2/9) Σ_μ G_μ τ G_μ†`, where
`(G_μ)_{(j,k),i} = δ_{ji}δ_{kμ} + ½δ_{jμ}δ_{ki} − ½δ_{μi}δ_{jk}`.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

open scoped ComplexOrder MatrixOrder BigOperators
open QIT

namespace QuanIncapacity

open QuanIncapacity

/- The Kraus operators of the defect, in the identification `Lin(ℂ³) ≃ ℂ³ ⊗ ℂ³`. -/
def G (μ : Fin 3) : Matrix (Prod (Fin 3) (Fin 3)) (Fin 3) ℂ :=
  Matrix.of fun jk i =>
    (if jk.1 = i then 1 else 0 : ℂ) * (if jk.2 = μ then 1 else 0)
    + (1 / 2 : ℂ) * (if jk.1 = μ then 1 else 0) * (if jk.2 = i then 1 else 0)
    - (1 / 2 : ℂ) * (if μ = i then 1 else 0) * (if jk.1 = jk.2 then 1 else 0)

/- The outer defect as a superoperator `Lin(ℂ³) → Lin(Lin(ℂ³)) ≃ Lin(ℂ³ ⊗ ℂ³)`. -/
def Δ : MatrixMap (Fin 3) (Prod (Fin 3) (Fin 3)) :=
  ((2 / 9 : ℝ) : ℂ) • MatrixMap.ofKraus (G : Fin 3 → Matrix (Prod (Fin 3) (Fin 3)) (Fin 3) ℂ)

/- Complete positivity of a positive scalar multiple of a CP map. -/
lemma smul_isCompletelyPositive {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {c : ℝ} (hc : 0 ≤ c) (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap.IsCompletelyPositive ((c : ℂ) • Phi) := by
  rw [MatrixMap.IsCompletelyPositive] at hPhi ⊢
  rw [show MatrixMap.choi ((c : ℂ) • Phi) = (c : ℂ) • MatrixMap.choi Phi by
    rfl]
  exact hPhi.smul (Complex.nonneg_iff.mpr ⟨by simpa using hc, by simp⟩)

/- The defect is completely positive (the exact CP-defect certificate). -/
lemma Δ_completelyPositive : MatrixMap.IsCompletelyPositive Δ := by
  dsimp [Δ]
  have hc : (0 : ℝ) ≤ (2 / 9 : ℝ) := by norm_num
  exact smul_isCompletelyPositive hc
    (MatrixMap.ofKraus (G : Fin 3 → Matrix (Prod (Fin 3) (Fin 3)) (Fin 3) ℂ))
    (MatrixMap.ofKraus_completelyPositive (G : Fin 3 → Matrix (Prod (Fin 3) (Fin 3)) (Fin 3) ℂ))

/- The Hilbert–Schmidt adjoint `𝒥† : Lin(ℂ⁴) → Lin(ℂ³)` of the shadow map, in the
  explicit block form: for `Z = [[α, uᵀ],[v, C]]`,
  `𝒥†(Z) = ((α + 2 Tr C)/3)𝟙₃ + (√2/3) Σ_μ (u_μ − v_μ) A_μ − (1/3) C − (2/3) Cᵀ`.
  `Qutrit/Adjoint` proves that this formula equals the general Hilbert–Schmidt
  adjoint. `Qutrit/CompleteShadow` connects the actual outer defect to the
  component formula and proves the arbitrary-reference instance. -/
def shadowAdjointEntries (Z : CMatrix (Fin 4)) : CMatrix (Fin 3) := Matrix.of fun μ ν =>
    ((Z 0 0 + 2 * (∑ ρ : Fin 3, Z (fin3ToFin4 ρ) (fin3ToFin4 ρ))) / 3)
      * (if μ = ν then 1 else 0 : ℂ)
    + (Real.sqrt 2 : ℂ) / 3 * (∑ ρ : Fin 3,
        (Z 0 (fin3ToFin4 ρ) - Z (fin3ToFin4 ρ) 0) * A ρ μ ν)
    - (1 / 3 : ℂ) * Z (fin3ToFin4 μ) (fin3ToFin4 ν)
    - (2 / 3 : ℂ) * Z (fin3ToFin4 ν) (fin3ToFin4 μ)
def 𝒥adj : MatrixMap (Fin 4) (Fin 3) where
  toFun := shadowAdjointEntries
  map_add' Y Z := by
    ext μ ν
    change shadowAdjointEntries (Y + Z) μ ν =
      shadowAdjointEntries Y μ ν + shadowAdjointEntries Z μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [shadowAdjointEntries, A, levN, fin3ToFin4, sum_univ_three, add_ite, ite_add, mul_ite, add_mul, mul_add]
    all_goals ring
  map_smul' c Z := by
    ext μ ν
    change shadowAdjointEntries (c • Z) μ ν = c * shadowAdjointEntries Z μ ν
    fin_cases μ <;> fin_cases ν <;>
      simp [shadowAdjointEntries, A, levN, fin3ToFin4, sum_univ_three, add_ite, ite_add, mul_ite, mul_assoc]
    all_goals ring

/- The outer defect expressed as the paper's component formula (Eq. S80), which is the
  explicit expansion of `L_{Λ(τ)} − 𝒥†∘L_{Λᶜ(τ)}∘𝒥`. -/
def defectEntries (τ : CMatrix (Fin 3)) : CMatrix (Fin 3 × Fin 3) := Matrix.of fun jk pq =>
    (2 / 9 : ℂ) * (
      (if jk.2 = pq.2 then 1 else 0) * τ jk.1 pq.1
      + (1 / 2 : ℂ) * (if jk.2 = pq.1 then 1 else 0) * τ jk.1 pq.2
      - (1 / 2 : ℂ) * (if pq.1 = pq.2 then 1 else 0) * τ jk.1 jk.2
      + (1 / 2 : ℂ) * (if jk.1 = pq.2 then 1 else 0) * τ jk.2 pq.1
      + (1 / 4 : ℂ) * (if jk.1 = pq.1 then 1 else 0) * τ jk.2 pq.2
      - (1 / 4 : ℂ) * (if pq.1 = pq.2 then 1 else 0) * τ jk.2 jk.1
      - (1 / 2 : ℂ) * (if jk.1 = jk.2 then 1 else 0) * τ pq.2 pq.1
      - (1 / 4 : ℂ) * (if jk.1 = jk.2 then 1 else 0) * τ pq.1 pq.2
      + (1 / 4 : ℂ) * (if jk.1 = jk.2 then 1 else 0) * (if pq.1 = pq.2 then 1 else 0) * (Matrix.trace τ : ℂ)
    )
def Δ_defect : MatrixMap (Fin 3) (Prod (Fin 3) (Fin 3)) where
  toFun := defectEntries
  map_add' τ τ' := by
    ext jk pq
    change defectEntries (τ + τ') jk pq = defectEntries τ jk pq + defectEntries τ' jk pq
    simp only [defectEntries, Matrix.of_apply, Matrix.add_apply, Matrix.trace_add]
    ring
  map_smul' c τ := by
    ext jk pq
    change defectEntries (c • τ) jk pq = c * defectEntries τ jk pq
    simp only [defectEntries, Matrix.of_apply, Matrix.smul_apply, Matrix.trace_smul,
      smul_eq_mul]
    ring

@[simp] lemma Δ_defect_apply (τ : CMatrix (Fin 3)) (jk pq : Fin 3 × Fin 3) :
    Δ_defect τ jk pq = defectEntries τ jk pq := rfl

/- The exact CP-defect factorization: the defect equals the Kraus form `(2/9)Σ_μ G_μ τ G_μ†`. -/
lemma Δ_defect_eq_Δ : Δ_defect = Δ := by
  ext τ jk pq
  rcases jk with ⟨j, k⟩
  rcases pq with ⟨p, q⟩
  fin_cases j <;> fin_cases k <;> fin_cases p <;> fin_cases q <;>
    simp [defectEntries, Δ, G, Matrix.trace, MatrixMap.ofKraus, Matrix.mul_apply,
      Matrix.conjTranspose, Matrix.sum_apply, sum_univ_three] <;>
    norm_num [map_ofNat] <;>
    ring

end QuanIncapacity
