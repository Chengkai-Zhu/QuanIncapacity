import QuanIncapacity.Qutrit.Lambda
import QIT.Information.Entropy.BinaryEntropy
import QIT.Core.Map.ChoiCharacterization

/-!
# The PPT activation partner

Tensor order is `(AB)(A'B')` until `regrouped`, then `(AA')(BB')`.
The four shield states define a normalized Choi state that is invariant under
partial transposition on the complete receiver `BB'`.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators
open QIT

namespace QuanIncapacity

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/- A qubit and a two-qubit (4-dimensional) system. -/
abbrev Qubit := Fin 2
abbrev Q4 := Qubit × Qubit

/- The bijection `Fin 4 ≃ Qubit × Qubit`, little-endian: `i ↦ (i % 2, i / 2)`. -/
def to2 (i : Fin 4) : Q4 :=
  (⟨i.1 % 2, by omega⟩, ⟨i.1 / 2, by omega⟩)

/- The inverse of `to2`. -/
def to4 (p : Q4) : Fin 4 :=
  ⟨p.1.1 + 2 * p.2.1, by omega⟩

/- `q_H = 2 - √2`. -/
def qH : ℝ := 2 - Real.sqrt 2

/- `(√2)^{-1}` as a complex scalar, used to normalize the Bell vectors. -/
def invSqrt2 : ℂ := (Real.sqrt 2 : ℂ)⁻¹

private lemma sqrt_two_pow_three : (Real.sqrt 2 : ℂ) ^ 3 = 2 * (Real.sqrt 2 : ℂ) := by
  calc
    _ = (Real.sqrt 2 : ℂ) ^ 2 * (Real.sqrt 2 : ℂ) := by ring
    _ = _ := by rw [sqrt_two_sq]

private lemma sqrt_two_pow_four : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
  calc
    _ = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
    _ = 4 := by rw [sqrt_two_sq]; norm_num

private lemma sqrt_two_pow_five : (Real.sqrt 2 : ℂ) ^ 5 = 4 * (Real.sqrt 2 : ℂ) := by
  calc
    _ = (Real.sqrt 2 : ℂ) ^ 4 * (Real.sqrt 2 : ℂ) := by ring
    _ = _ := by rw [sqrt_two_pow_four]

/- Real-arithmetic lemmas: `1 ≤ √2 ≤ 2`, hence `0 ≤ q_H ≤ 1`. -/
lemma sqrt_two_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
  rwa [Real.sqrt_one] at h

lemma sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 2 ^ 2)
  have h4 : Real.sqrt (2 ^ 2) = 2 := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
  rwa [h4] at h

lemma qH_nonneg : 0 ≤ qH := by
  unfold qH
  nlinarith [sqrt_two_le_two]

lemma qH_le_one : qH ≤ 1 := by
  unfold qH
  nlinarith [sqrt_two_ge_one]

lemma qH_half_nonneg : 0 ≤ (qH / 2 : ℝ) := div_nonneg qH_nonneg (by norm_num)

lemma qH_quarter_nonneg : 0 ≤ (qH / 4 : ℝ) := div_nonneg qH_nonneg (by norm_num)

lemma one_sub_qH_half_nonneg : 0 ≤ ((1 - qH) / 2 : ℝ) := by
  have h : 0 ≤ 1 - qH := by nlinarith [qH_le_one]
  exact div_nonneg h (by norm_num)

/- Strict bounds: `1 < √2 < 2`, hence `0 < q_H < 1`. -/
lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h := Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (2 : ℝ)) (by norm_num : (2 : ℝ) < 2 ^ 2)
  simpa [Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))] using h

lemma one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h := Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) < 2)
  simpa [Real.sqrt_one] using h

lemma qH_pos : 0 < qH := by
  unfold qH
  nlinarith [sqrt_two_lt_two]

lemma qH_lt_one : qH < 1 := by
  unfold qH
  nlinarith [one_lt_sqrt_two]

lemma qH_ne_half : qH ≠ (2 : ℝ)⁻¹ := by
  intro h
  unfold qH at h
  have hsq : (Real.sqrt 2)^2 = (3 / 2 : ℝ)^2 := by
    nlinarith [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, h]
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/- Sum over the four elements of `Q4 = Qubit × Qubit`. -/
@[simp]
lemma sum_univ_q4 {M : Type*} [AddCommMonoid M] (f : Q4 → M) :
    (∑ i : Q4, f i) = f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1) := by
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, add_assoc]

/- The four Bell vectors `β₀ = Φ⁺, β₁ = Φ⁻, β₂ = Ψ⁺, β₃ = Ψ⁻` on `Q4`. -/
def beta : Fin 4 → Q4 → ℂ :=
  fun j p =>
    if j = 0 then (if p.1 = p.2 then invSqrt2 else 0)
    else if j = 1 then (if p.1 = p.2 then (if p.1 = 0 then invSqrt2 else -invSqrt2) else 0)
    else if j = 2 then (if p.1 ≠ p.2 then invSqrt2 else 0)
    else (if p.1 ≠ p.2 then (if p.1 = 0 then -invSqrt2 else invSqrt2) else 0)

/- The rank-one Bell projectors `β_j β_j†`. -/
def bellProj (j : Fin 4) : Matrix Q4 Q4 ℂ :=
  Matrix.vecMulVec (beta j) (star (beta j))

/- Shield projectors written with algebraic entries. For j=2,3 these are exactly
|χ₊⟩⟨χ₊| and |χ₋⟩⟨χ₋| from the paper, after multiplying the square roots. -/
def tau (j : Fin 4) : Matrix Q4 Q4 ℂ :=
  if j = 0 then
    (1 / 2 : ℂ) • (Matrix.single (0, 0) (0, 0) 1 + bellProj 2)
  else if j = 1 then
    (1 / 2 : ℂ) • (Matrix.single (1, 1) (1, 1) 1 + bellProj 3)
  else if j = 2 then
    Matrix.of fun p q ↦ if p = (0, 0) then
      (if q = (0, 0) then (2 + (Real.sqrt 2 : ℂ)) / 4
       else if q = (1, 1) then (Real.sqrt 2 : ℂ) / 4 else 0)
    else if p = (1, 1) then
      (if q = (0, 0) then (Real.sqrt 2 : ℂ) / 4
       else if q = (1, 1) then (2 - (Real.sqrt 2 : ℂ)) / 4 else 0)
    else 0
  else
    Matrix.of fun p q ↦ if p = (0, 0) then
      (if q = (0, 0) then (2 - (Real.sqrt 2 : ℂ)) / 4
       else if q = (1, 1) then -(Real.sqrt 2 : ℂ) / 4 else 0)
    else if p = (1, 1) then
      (if q = (0, 0) then -(Real.sqrt 2 : ℂ) / 4
       else if q = (1, 1) then (2 + (Real.sqrt 2 : ℂ)) / 4 else 0)
    else 0

lemma bellProj_posSemidef (j : Fin 4) : (bellProj j).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (beta j)

/-- An exact Gram certificate, including the rank-two shields. -/
lemma tau_gram (j : Fin 4) :
    tau j = (if j = 0 ∨ j = 1 then (2 : ℝ) else 1) •
      ((tau j).conjTranspose * tau j) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [tau, bellProj, beta, invSqrt2, sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecMulVec, Matrix.smul_apply]
  all_goals norm_num [map_ofNat]
  all_goals try ring_nf
  all_goals try simp only [sqrt_two_sq, sqrt_two_pow_three, sqrt_two_pow_four, sqrt_two_pow_five, map_ofNat]
  all_goals ring

lemma tau_posSemidef (j : Fin 4) : (tau j).PosSemidef := by
  rw [tau_gram j]
  exact (Matrix.posSemidef_conjTranspose_mul_self (tau j)).smul (by split_ifs <;> norm_num)

def OmegaH : Matrix (Q4 × Q4) (Q4 × Q4) ℂ :=
  (qH / 2 : ℝ) • (Matrix.kronecker (bellProj 0) (tau 0) +
    Matrix.kronecker (bellProj 1) (tau 1)) +
  ((1 - qH) / 2 : ℝ) • (Matrix.kronecker (bellProj 2) (tau 2) +
    Matrix.kronecker (bellProj 3) (tau 3))

lemma Omega_posSemidef : OmegaH.PosSemidef := by
  exact (((bellProj_posSemidef 0).kronecker (tau_posSemidef 0)).add
    ((bellProj_posSemidef 1).kronecker (tau_posSemidef 1))).smul qH_half_nonneg |>.add
    ((((bellProj_posSemidef 2).kronecker (tau_posSemidef 2)).add
    ((bellProj_posSemidef 3).kronecker (tau_posSemidef 3))).smul one_sub_qH_half_nonneg)

/-- Partial transpose on both receiver qubits in the original tensor order. -/
def ptBB' (M : Matrix (Q4 × Q4) (Q4 × Q4) ℂ) : Matrix (Q4 × Q4) (Q4 × Q4) ℂ :=
  Matrix.of fun p q ↦ M ((p.1.1, q.1.2), (p.2.1, q.2.2))
    ((q.1.1, p.1.2), (q.2.1, p.2.2))

lemma Omega_partialTranspose_invariant : ptBB' OmegaH = OmegaH := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨e, f⟩, ⟨g, h⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases e <;> fin_cases f <;> fin_cases g <;> fin_cases h <;>
    simp [ptBB', OmegaH, tau, bellProj, beta, invSqrt2, sqrt_two_inv_eq_half_sqrt, qH, Matrix.kronecker,
      Matrix.vecMulVec, Matrix.smul_apply, Matrix.add_apply]
  all_goals norm_num [map_ofNat]
  all_goals try ring_nf
  all_goals try simp only [sqrt_two_sq, sqrt_two_pow_three, sqrt_two_pow_four, sqrt_two_pow_five, map_ofNat]
  all_goals ring

lemma Omega_pt_posSemidef : (ptBB' OmegaH).PosSemidef := by
  rw [Omega_partialTranspose_invariant]
  exact Omega_posSemidef

def regrouped (M : Matrix (Q4 × Q4) (Q4 × Q4) ℂ) : Matrix (Q4 × Q4) (Q4 × Q4) ℂ :=
  Matrix.of fun p q ↦ M ((p.1.1, p.2.1), (p.1.2, p.2.2)) ((q.1.1, q.2.1), (q.1.2, q.2.2))

lemma Omega_marginal :
    partialTraceB (regrouped OmegaH) = (1 / 4 : ℂ) • (1 : Matrix Q4 Q4 ℂ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [partialTraceB, regrouped, OmegaH, tau, bellProj, beta, invSqrt2, sqrt_two_inv_eq_half_sqrt, qH,
      Matrix.kronecker, Matrix.vecMulVec, Matrix.smul_apply, Matrix.add_apply]
  all_goals norm_num [map_ofNat]
  all_goals try ring_nf
  all_goals try simp only [sqrt_two_sq, sqrt_two_pow_three, sqrt_two_pow_four, sqrt_two_pow_five, map_ofNat]
  all_goals ring

def JH : Matrix (Q4 × Q4) (Q4 × Q4) ℂ := (4 : ℝ) • regrouped OmegaH

def M_H_map : MatrixMap Q4 Q4 := MatrixMap.ofChoiMatrix JH

lemma JH_posSemidef : JH.PosSemidef := by
  exact (Omega_posSemidef.submatrix
    (fun p : Q4 × Q4 ↦ ((p.1.1, p.2.1), (p.1.2, p.2.2)))).smul (by norm_num)

lemma M_H_completelyPositive : MatrixMap.IsCompletelyPositive M_H_map :=
  MatrixMap.ofChoiMatrix_isCompletelyPositive JH_posSemidef

lemma M_H_tracePreserving : MatrixMap.IsTracePreserving M_H_map := by
  apply MatrixMap.isTracePreserving_iff_partialTraceB_choi M_H_map |>.mpr
  rw [M_H_map, MatrixMap.choi_ofChoiMatrix]
  change partialTraceB ((4 : ℂ) • regrouped OmegaH) = 1
  rw [partialTraceB_smul, Omega_marginal, smul_smul]
  norm_num

/-- The actual CPTP channel with the paper's Choi matrix. -/
def M_H : Channel Q4 Q4 where
  map := M_H_map
  completelyPositive := M_H_completelyPositive
  tracePreserving := M_H_tracePreserving
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ M_H_completelyPositive

lemma M_H_choi : MatrixMap.choi M_H.map = JH := MatrixMap.choi_ofChoiMatrix JH

/-- PPT across the input/output partition of the actual channel's Choi matrix. -/
theorem M_H_choi_ppt : (partialTransposeB (MatrixMap.choi M_H.map)).PosSemidef := by
  rw [M_H_choi]
  have heq : partialTransposeB JH = JH := by
    change (4 : ℝ) • regrouped (ptBB' OmegaH) = (4 : ℝ) • regrouped OmegaH
    rw [Omega_partialTranspose_invariant]
  rw [heq]
  exact JH_posSemidef

/-- This only proves positivity of a scalar expression. The equality to the private
information of the specified ensemble is a separate, currently unformalized bridge. -/
lemma helper_entropy_gap_pos : 0 < 1 - QIT.binaryEntropy qH := by
  rw [QIT.binaryEntropy_eq_binEntropy_div_log_two]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlt : Real.binEntropy qH < Real.log 2 := Real.binEntropy_lt_log_two.mpr qH_ne_half
  have hdiv : Real.binEntropy qH / Real.log 2 < 1 := (div_lt_one hlog).mpr hlt
  linarith

end QuanIncapacity
