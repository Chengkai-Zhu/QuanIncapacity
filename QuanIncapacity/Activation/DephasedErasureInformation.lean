import QuanIncapacity.Activation.DephasedErasureChannel
import QuanIncapacity.Activation.OrthogonalFlags

/-! Coherent-information bounds for the actual dephased-erasure channel.
All three branch states are channel outputs on the same arbitrary joint input. -/

noncomputable section
open QIT
open scoped BigOperators NNReal

namespace QuanIncapacity.DephasedErasure

variable {r b c : Type} [Fintype r] [DecidableEq r]
variable [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

def output (ρ : State (r × (b × c))) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    State (r × (b × Option c)) :=
  ((Channel.idChannel r).prod
    ((Channel.idChannel b).prod (channel q η hq0 hq1 hη0 hη1))).applyState ρ

theorem output_matrix (ρ : State (r × (b × c))) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (x y : r) (u v : b) (i j : Option c) :
    (output ρ q η hq0 hq1 hη0 hη1).matrix (x, (u, i)) (y, (v, j)) =
      matrix q η (fun k l ↦ ρ.matrix (x, (u, k)) (y, (v, l))) i j := by
  calc
    _ = ((Channel.idChannel b).prod (channel q η hq0 hq1 hη0 hη1)).map
        (fun k l ↦ ρ.matrix (x, k) (y, l)) (u, i) (v, j) :=
      MatrixMap.kron_idChannel_left_apply_slice _ ρ.matrix (x, (u, i)) (y, (v, j))
    _ = (channel q η hq0 hq1 hη0 hη1).map
        (fun k l ↦ ρ.matrix (x, (u, k)) (y, (v, l))) i j :=
      MatrixMap.kron_idChannel_left_apply_slice _ (fun k l ↦ ρ.matrix (x, k) (y, l))
        (u, i) (v, j)
    _ = _ := by rw [channel_map]; rfl

def success (ρ : State (r × (b × c))) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :=
  output ρ 1 η (by norm_num) le_rfl hη0 hη1

def erase (ρ : State (r × (b × c))) := output ρ 0 0 le_rfl (by norm_num) le_rfl (by norm_num)

def identityBranch (ρ : State (r × (b × c))) := success ρ 1 (by norm_num) le_rfl

def dephasedBranch (ρ : State (r × (b × c))) := success ρ 0 le_rfl (by norm_num)

theorem output_eq_binaryMix (ρ : State (r × (b × c))) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    output ρ q η hq0 hq1 hη0 hη1 =
      State.binaryMix q (erase ρ) (success ρ η hη0 hη1) hq0 hq1 := by
  apply State.ext
  ext ⟨x, u, i⟩ ⟨y, v, j⟩
  simp only [State.binaryMix_matrix, Matrix.add_apply, Matrix.smul_apply,
    NNReal.smul_def, Real.toNNReal_of_nonneg hq0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hq1), Complex.real_smul,
    success, erase, output_matrix]
  cases i <;> cases j <;> simp [matrix, Complex.ofReal_sub] <;> ring

theorem success_eq_binaryMix (ρ : State (r × (b × c))) (η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    success ρ η hη0 hη1 =
      State.binaryMix η (dephasedBranch ρ) (identityBranch ρ) hη0 hη1 := by
  apply State.ext
  ext ⟨x, u, i⟩ ⟨y, v, j⟩
  simp only [State.binaryMix_matrix, Matrix.add_apply, Matrix.smul_apply,
    NNReal.smul_def, Real.toNNReal_of_nonneg hη0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hη1), Complex.real_smul,
    identityBranch, dephasedBranch, success, output_matrix]
  cases i <;> cases j <;> simp [matrix, Complex.ofReal_sub] <;> ring

def branchEnsemble (ρ : State (r × (b × c))) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    Ensemble Bool (r × (b × Option c)) where
  probs t := if t then ⟨q, hq0⟩ else ⟨1 - q, sub_nonneg.mpr hq1⟩
  weights_sum := by
    change (∑ t : Bool, if t then (⟨q, hq0⟩ : ℝ≥0) else ⟨1 - q, sub_nonneg.mpr hq1⟩) = 1
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    apply Subtype.ext
    change q + (1 - q) = 1
    ring
  states t := if t then success ρ η hη0 hη1 else erase ρ

theorem branchEnsemble_average (ρ : State (r × (b × c))) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (branchEnsemble ρ q η hq0 hq1 hη0 hη1).averageState =
      output ρ q η hq0 hq1 hη0 hη1 := by
  rw [output_eq_binaryMix]
  apply State.ext
  ext i j
  simp [branchEnsemble, State.binaryMix_matrix, Real.toNNReal_of_nonneg hq0,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hq1), Matrix.add_apply, Matrix.smul_apply,
    NNReal.smul_def, NNReal.coe_mk, Complex.real_smul, Complex.ofReal_sub, add_comm]
  change ((1 - q : ℝ) : ℂ) * (erase ρ).matrix i j +
    (q : ℂ) * (success ρ η hη0 hη1).matrix i j =
    (1 - (q : ℂ)) * (erase ρ).matrix i j + (q : ℂ) * (success ρ η hη0 hη1).matrix i j
  rw [Complex.ofReal_sub, Complex.ofReal_one]

/-- The erasure flag is actually present in the channel output. -/
theorem output_coherentInformation (ρ : State (r × (b × c))) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (output ρ q η hq0 hq1 hη0 hη1).coherentInformation =
      q * (success ρ η hη0 hη1).coherentInformation + (1 - q) * (erase ρ).coherentInformation := by
  let E := branchEnsemble ρ q η hq0 hq1 hη0 hη1
  have hs : ∀ (t : Bool) (x y : r) (u v : b × Option c),
      u.2.isSome ≠ t ∨ v.2.isSome ≠ t →
        (E.states t).matrix (x, u) (y, v) = 0 := by
    intro t x y ⟨u, i⟩ ⟨v, j⟩ ht
    cases t <;> cases i <;> cases j <;>
      simp_all [E, branchEnsemble, success, erase, output_matrix, matrix]
  have hh := Activation.coherentInformation_average_orthogonal E (fun u ↦ u.2.isSome) hs
  change (branchEnsemble ρ q η hq0 hq1 hη0 hη1).averageState.coherentInformation = _ at hh
  rw [branchEnsemble_average, Fintype.sum_bool] at hh
  exact hh

/-- Universal three-branch bound before specializing the conditional purification.
The mixing penalty is binary and independent of the dimension of `c`. -/
theorem output_coherentInformation_ge (ρ : State (r × (b × c))) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    q * η * (identityBranch ρ).coherentInformation +
        q * (1 - η) * (dephasedBranch ρ).coherentInformation - q * binaryEntropy η +
        (1 - q) * (erase ρ).coherentInformation ≤
      (output ρ q η hq0 hq1 hη0 hη1).coherentInformation := by
  have hh := Activation.coherentInformation_binaryMix_ge η (dephasedBranch ρ)
    (identityBranch ρ) hη0 hη1
  rw [← success_eq_binaryMix] at hh
  rw [output_coherentInformation]
  nlinarith [mul_le_mul_of_nonneg_left hh hq0]

end QuanIncapacity.DephasedErasure
