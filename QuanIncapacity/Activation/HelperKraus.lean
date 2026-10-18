import QuanIncapacity.Activation.HelperChannel
import QuanIncapacity.Framework.ChannelPair

/-! A six-Kraus representation of the actual PPT helper, with its entire
six-dimensional Stinespring environment retained. -/

noncomputable section
open QIT
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace QuanIncapacity.Helper

def alpha : ℝ := Real.sqrt (2 + Real.sqrt 2) / 2
def betaCoeff : ℝ := Real.sqrt (2 - Real.sqrt 2) / 2
def weightQ : ℝ := Real.sqrt (qH / 2)
def weightE : ℝ := Real.sqrt (1 - qH)

theorem alpha_square : (alpha : ℂ) ^ 2 = (2 + (Real.sqrt 2 : ℂ)) / 4 := by
  have h : alpha ^ 2 = (2 + Real.sqrt 2) / 4 := by
    unfold alpha
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  exact_mod_cast h

theorem beta_square : (betaCoeff : ℂ) ^ 2 = (2 - (Real.sqrt 2 : ℂ)) / 4 := by
  have h : betaCoeff ^ 2 = (2 - Real.sqrt 2) / 4 := by
    unfold betaCoeff
    rw [div_pow, Real.sq_sqrt (by nlinarith [sqrt_two_le_two])]
    norm_num
  exact_mod_cast h

theorem alpha_beta : (alpha : ℂ) * (betaCoeff : ℂ) = (Real.sqrt 2 : ℂ) / 4 := by
  have hp : Real.sqrt (2 + Real.sqrt 2) * Real.sqrt (2 - Real.sqrt 2) = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h : alpha * betaCoeff = Real.sqrt 2 / 4 := by
    unfold alpha betaCoeff
    nlinarith
  exact_mod_cast h

theorem beta_alpha : (betaCoeff : ℂ) * (alpha : ℂ) = (Real.sqrt 2 : ℂ) / 4 := by
  rw [mul_comm, alpha_beta]

theorem weightQ_square : (weightQ : ℂ) ^ 2 = (qH : ℂ) / 2 := by
  have h : weightQ ^ 2 = qH / 2 := Real.sq_sqrt qH_half_nonneg
  exact_mod_cast h

theorem weightE_square : (weightE : ℂ) ^ 2 = 1 - (qH : ℂ) := by
  have h : weightE ^ 2 = 1 - qH := Real.sq_sqrt (sub_nonneg.mpr qH_le_one)
  exact_mod_cast h

def key (l : Fin 6) : CMatrix Qubit :=
  if l = 0 ∨ l = 1 then 1
  else if l = 2 ∨ l = 3 then Matrix.diagonal ![1, -1]
  else if l = 4 then !![0, 1; 1, 0]
  else !![0, 1; -1, 0]

def shield (l : Fin 6) : CMatrix Qubit :=
  if l = 0 then Matrix.single 0 0 1
  else if l = 1 then Matrix.of fun j i ↦ QuanIncapacity.beta 2 (i, j)
  else if l = 2 then Matrix.single 1 1 1
  else if l = 3 then Matrix.of fun j i ↦ QuanIncapacity.beta 3 (i, j)
  else if l = 4 then Matrix.diagonal ![(alpha : ℂ), (betaCoeff : ℂ)]
  else Matrix.diagonal ![(betaCoeff : ℂ), -(alpha : ℂ)]

def kraus (l : Fin 6) : CMatrix Q4 :=
  (if l.val < 4 then (weightQ : ℂ) else (weightE : ℂ)) • (key l).kronecker (shield l)

def gram (S : CMatrix Qubit) : CMatrix Q4 :=
  Matrix.of fun p q ↦ S p.2 p.1 * star (S q.2 q.1)

set_option maxHeartbeats 800000 in
theorem key_gram (l : Fin 6) :
    gram (key l) = (2 : ℂ) • bellProj
      (if l = 0 ∨ l = 1 then 0 else if l = 2 ∨ l = 3 then 1 else if l = 4 then 2 else 3) := by
  ext ⟨i, j⟩ ⟨k, m⟩
  fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;>
    norm_num [gram, key, bellProj, QuanIncapacity.beta, invSqrt2,
      sqrt_two_inv_eq_half_sqrt, Matrix.vecMulVec, Matrix.smul_apply, map_ofNat]
  all_goals ring_nf
  all_goals simp only [sqrt_two_sq]
  all_goals norm_num

set_option maxHeartbeats 800000 in
theorem shield_gram (l : Fin 6) :
    gram (shield l) =
      if l = 0 then Matrix.single (0, 0) (0, 0) 1
      else if l = 1 then bellProj 2
      else if l = 2 then Matrix.single (1, 1) (1, 1) 1
      else if l = 3 then bellProj 3
      else if l = 4 then tau 2 else tau 3 := by
  ext ⟨i, j⟩ ⟨k, m⟩
  fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;>
    simp [gram, shield, tau, bellProj, QuanIncapacity.beta, invSqrt2,
      Matrix.vecMulVec, Matrix.single, Complex.star_def, Complex.conj_ofReal]
  all_goals norm_num [map_ofNat]
  all_goals ring_nf
  all_goals try simp only [alpha_square, beta_square, alpha_beta, beta_alpha, sqrt_two_inv_sq]
  all_goals ring

theorem kraus_choi_sum : MatrixMap.choi (MatrixMap.ofKraus kraus) =
    ∑ l : Fin 6, (if l.val < 4 then (qH : ℂ) / 2 else 1 - (qH : ℂ)) •
      regrouped ((gram (key l)).kronecker (gram (shield l))) := by
  rw [MatrixMap.choi_ofKraus]
  ext p q
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  fin_cases l <;>
    simp [kraus, gram, regrouped, Matrix.vecMulVec, Matrix.kronecker, Matrix.smul_apply,
      Complex.star_def, Complex.conj_ofReal]
  all_goals ring_nf
  all_goals simp only [weightQ_square, weightE_square]
  all_goals ring

theorem tau_zero : tau 0 = (1 / 2 : ℂ) •
    (Matrix.single (0, 0) (0, 0) 1 + bellProj 2) := by simp [tau]

theorem tau_one : tau 1 = (1 / 2 : ℂ) •
    (Matrix.single (1, 1) (1, 1) 1 + bellProj 3) := by simp [tau]

theorem kraus_choi : MatrixMap.choi (MatrixMap.ofKraus kraus) = JH := by
  rw [kraus_choi_sum]
  simp_rw [key_gram, shield_gram]
  ext p q
  simp [Fin.sum_univ_succ, JH, regrouped, OmegaH, tau_zero, tau_one,
    Matrix.kronecker, Matrix.smul_apply, Matrix.add_apply]
  simp only [Matrix.single_apply]
  split_ifs <;> ring

theorem channel_map_eq : M_H.map = MatrixMap.ofKraus kraus := by
  apply MatrixMap.choi_inj
  rw [M_H_choi, kraus_choi]

theorem kraus_tracePreserving : MatrixMap.IsTracePreserving (MatrixMap.ofKraus kraus) := by
  rw [← channel_map_eq]
  exact M_H.tracePreserving

def dilation : ReferenceIsometry Q4 (Q4 × Fin 6) :=
  MatrixMap.krausStinespringIsometry kraus kraus_tracePreserving

def complement : Channel Q4 (Fin 6) := dilation.complementaryChannel

theorem complementary : ComplementaryChannels M_H complement := by
  refine ⟨dilation, ?_, rfl⟩
  apply dilation.outputChannel_eq_of_realizes
  intro X
  rw [channel_map_eq]
  exact (MatrixMap.partialTraceB_krausStinespringIsometry kraus kraus_tracePreserving X).symm

end QuanIncapacity.Helper
