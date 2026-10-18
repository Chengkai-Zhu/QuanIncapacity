import QuanIncapacity.Qutrit.Defect

/-!
# Complete observable shadowing and the variance/CP-defect criterion

The paper's Definition of complete observable shadowing (a statistical, observable-level
condition) and the Proposition that it is equivalent, via the outer defect, to a finite
second-moment / complete-positivity certificate. We formalize the scalar (no-reference)
forms and the qutrit instantiation, and record the reference-complete forms.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT

namespace QuanIncapacity

open QuanIncapacity

/- Variance of a Hermitian observable `Y` in a state `θ`: `Var_θ(Y) = Tr(θ Y²) − Tr(θ Y)²`. -/
noncomputable def Var {n : Type*} [Fintype n] [DecidableEq n]
    (θ Y : Matrix n n ℂ) : ℝ :=
  ((θ * Y * Y).trace).re - (((θ * Y).trace).re) ^ 2

/- The second-moment difference for a map `𝒥` between two channels (Schrödinger picture):
  `Tr(Z† 𝒩(τ) Z) − Tr(𝒥(Z)† 𝒩ᶜ(τ) 𝒥(Z))`. This is the scalar version of the paper's
  Eq. (S64); its nonnegativity for all `Z` and PSD `τ` certifies positivity, not complete positivity. -/
noncomputable def secondMomentDifference
    (N : MatrixMap (Fin 3) (Fin 3)) (Nc : MatrixMap (Fin 3) (Fin 4))
    (J : MatrixMap (Fin 3) (Fin 4))
    (τ Z : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  ((Z.conjTranspose * N τ * Z).trace).re
    - ((J Z).conjTranspose * Nc τ * J Z).trace.re

/- Flatten a 3×3 matrix into a vector indexed by `Prod (Fin 3) (Fin 3)`. -/
noncomputable def flat (Y : Matrix (Fin 3) (Fin 3) ℂ) : Prod (Fin 3) (Fin 3) → ℂ :=
  fun jk => Y jk.1 jk.2

private lemma complement_entry (ρ : CMatrix (Fin 3)) (a b : Fin 4) :
    Λc_map ρ a b = (K a * ρ * (K b).conjTranspose).trace := rfl

private lemma shadowing_sqrt_four : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
  calc
    _ = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
    _ = 4 := by rw [sqrt_two_sq]; norm_num

/- The means agree: `Tr(Λ ρ Y) = Tr(Λᶜ ρ (𝒥 Y))`. -/
lemma mean_agree (ρ Y : Matrix (Fin 3) (Fin 3) ℂ) :
    (Λ_map ρ * Y).trace = (Λc_map ρ * 𝒥_map Y).trace := by
  simp [Λ_map, complement_entry, shadowEntries, K, Ec, A, levN, avec, fin4ToFin3, fin3ToFin4,
    sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply, Matrix.trace, Matrix.transpose, Matrix.conjTranspose]
  change Fin 3 → Fin 3 → ℂ at ρ Y
  norm_num [map_ofNat]
  ring_nf
  try simp only [sqrt_two_sq, sqrt_two_inv_sq, map_ofNat]
  ring

/- The second-moment difference equals the quadratic form of the outer defect. -/
lemma secondMoment_eq_defect (ρ Y : Matrix (Fin 3) (Fin 3) ℂ) :
    (Y.conjTranspose * Λ_map ρ * Y).trace - ((𝒥_map Y).conjTranspose * Λc_map ρ * (𝒥_map Y)).trace
      = star (flat Y) ⬝ᵥ ((Δ_defect ρ) *ᵥ (flat Y)) := by
  apply sub_eq_zero.mp
  simp [flat, Λ_map, complement_entry, shadowEntries, K, Ec, A, levN, avec, defectEntries, fin4ToFin3, fin3ToFin4,
    sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply, Matrix.trace, Matrix.transpose,
    Matrix.conjTranspose, dotProduct, Matrix.mulVec, Fintype.sum_prod_type]
  change Fin 3 → Fin 3 → ℂ at ρ Y
  norm_num [map_ofNat]
  ring_nf
  try simp only [sqrt_two_sq, shadowing_sqrt_four, map_ofNat]
  ring

/- The outer defect applied to a PSD state is PSD. -/
lemma Δ_defect_psd (ρ : Matrix (Fin 3) (Fin 3) ℂ) (hρ : ρ.PosSemidef) :
    (Δ_defect ρ).PosSemidef := by
  simpa [Δ_defect_eq_Δ] using
    (MatrixMap.isCompletelyPositive_mapsPositive Δ Δ_completelyPositive ρ hρ)

/- **Scalar variance domination for the qutrit.** For every Hermitian `Y`, the environment
  estimator `𝒥(Y)` has no larger variance than `Y`:
  `Var_{Λ(ρ)}(Y) ≥ Var_{Λᶜ(ρ)}(𝒥(Y))`. This is the paper's Eq. (S89) (sum-of-squares)
  for the case of no reference, and follows from the completely positive outer defect. -/
theorem qutrit_variance_domination
    (ρ : Matrix (Fin 3) (Fin 3) ℂ) (hρ : ρ.PosSemidef)
    (Y : Matrix (Fin 3) (Fin 3) ℂ) (hY : Y.IsHermitian) :
    Var (Λ_map ρ) Y ≥ Var (Λc_map ρ) (𝒥_map Y) := by
  -- Both means agree by the lift identity `𝒥_lift`, so the variance difference is exactly
  -- the second-moment difference, which is nonnegative by the CP defect.
  have hYdag : Y.conjTranspose = Y := hY
  have hJY_herm : (𝒥_map Y).conjTranspose = 𝒥_map Y := by
    rw [← 𝒥_adjoint_preserving, hYdag]
  have hmean : (Λ_map ρ * Y).trace = (Λc_map ρ * 𝒥_map Y).trace := mean_agree ρ Y
  -- the second-moment difference (complex) equals the defect quadratic form
  have hsec : (Λ_map ρ * Y * Y).trace - (Λc_map ρ * 𝒥_map Y * 𝒥_map Y).trace
      = star (flat Y) ⬝ᵥ ((Δ_defect ρ) *ᵥ (flat Y)) := by
    have hA : (Λ_map ρ * Y * Y).trace = (Y.conjTranspose * Λ_map ρ * Y).trace := by
      rw [Matrix.trace_mul_cycle (Λ_map ρ) Y Y]
      congr 1; congr 1; congr 1
      exact hYdag.symm
    have hB : (Λc_map ρ * 𝒥_map Y * 𝒥_map Y).trace =
        ((𝒥_map Y).conjTranspose * Λc_map ρ * (𝒥_map Y)).trace := by
      rw [Matrix.trace_mul_cycle (Λc_map ρ) (𝒥_map Y) (𝒥_map Y)]
      congr 1; congr 1; congr 1
      exact hJY_herm.symm
    rw [hA, hB]
    exact secondMoment_eq_defect ρ Y
  -- the defect quadratic form is nonnegative (real part) since Δ_defect ρ ⪰ 0
  have hD : (Δ_defect ρ).PosSemidef := Δ_defect_psd ρ hρ
  have hnn : 0 ≤ star (flat Y) ⬝ᵥ ((Δ_defect ρ) *ᵥ (flat Y)) :=
    hD.dotProduct_mulVec_nonneg (flat Y)
  have hnn_re : 0 ≤ (star (flat Y) ⬝ᵥ ((Δ_defect ρ) *ᵥ (flat Y))).re :=
    (Complex.nonneg_iff.mp hnn).1
  have hsec_re : ((Λ_map ρ * Y * Y).trace).re - ((Λc_map ρ * 𝒥_map Y * 𝒥_map Y).trace).re
      = (star (flat Y) ⬝ᵥ ((Δ_defect ρ) *ᵥ (flat Y))).re := by
    rw [← Complex.sub_re]
    exact congrArg Complex.re hsec
  -- now assemble the variance inequality
  unfold Var
  have hmean_re : ((Λ_map ρ * Y).trace).re = ((Λc_map ρ * 𝒥_map Y).trace).re := by rw [hmean]
  rw [hmean_re]
  apply sub_le_sub_right
  apply sub_nonneg.mp
  rw [hsec_re]
  exact hnn_re

/-- Scalar shadowing includes adjoint preservation, unbiasedness, and variance domination.
It is weaker than complete shadowing; no reference-system quantifier is implicit. -/
def IsScalarShadowMap (N : MatrixMap (Fin 3) (Fin 3))
    (M : MatrixMap (Fin 3) (Fin 4)) (J : MatrixMap (Fin 3) (Fin 4)) : Prop :=
  (∀ Y, J Y.conjTranspose = (J Y).conjTranspose) ∧
  (∀ ρ Y, (N ρ * Y).trace = (M ρ * J Y).trace) ∧
  (∀ ρ, ρ.PosSemidef → ∀ Y, Y.IsHermitian → Var (M ρ) (J Y) ≤ Var (N ρ) Y)

/-- The paper's reference-complete predicate, with all finite matrix reference systems
represented by `Fin r`. The general amplification-to-defect equivalence is proved
in `Framework/HermitianDilation`. -/
def IsCompleteShadowMap (N : MatrixMap (Fin 3) (Fin 3))
    (M : MatrixMap (Fin 3) (Fin 4)) (J : MatrixMap (Fin 3) (Fin 4)) : Prop :=
  (∀ Y, J Y.conjTranspose = (J Y).conjTranspose) ∧
  (∀ ρ Y, (N ρ * Y).trace = (M ρ * J Y).trace) ∧
  ∀ r : ℕ, ∀ ρ : State (Fin r × Fin 3), ∀ Y : CMatrix (Fin r × Fin 3),
    Y.IsHermitian →
      Var ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin r) (Fin r)) M) ρ.matrix)
          ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin r) (Fin r)) J) Y) ≤
        Var ((MatrixMap.kron (LinearMap.id : MatrixMap (Fin r) (Fin r)) N) ρ.matrix) Y

/-- The established scalar certificate; this does not assert complete shadowing. -/
lemma qutrit_scalar_shadow_map : IsScalarShadowMap Λ_map Λc_map 𝒥_map := by
  exact ⟨𝒥_adjoint_preserving, mean_agree, qutrit_variance_domination⟩

end QuanIncapacity
