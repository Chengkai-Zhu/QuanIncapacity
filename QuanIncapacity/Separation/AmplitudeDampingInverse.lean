import QuanIncapacity.Separation.AmplitudeDamping

noncomputable section
open QIT
open QuanIncapacity.MatrixSpace
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity.AmplitudeDamping

def complementInverse (γ : ℝ) : MatrixMap (Fin 2) (Fin 2) where
  toFun X :=
    !![X 0 0 - ((1 - (γ : ℂ)) / (γ : ℂ)) * X 1 1,
        X 0 1 / (Real.sqrt γ : ℂ);
      X 1 0 / (Real.sqrt γ : ℂ), X 1 1 / (γ : ℂ)]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply] <;> ring
  map_smul' z X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, smul_eq_mul] <;> ring

theorem complement_inverse_right (γ : ℝ) (h0 : 0 < γ) (h1 : γ ≤ 1)
    (X : CMatrix (Fin 2)) :
    (channel (1 - γ) (sub_nonneg.mpr h1) (by linarith)).map
      (complementInverse γ X) = X := by
  rw [channel_apply]
  have hγ : (γ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
  have hs : (Real.sqrt γ : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr h0)
  have hg : 1 - (1 - γ) = γ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complementInverse, hg]
  all_goals push_cast
  all_goals field_simp
  all_goals ring

theorem complement_inverse_left (γ : ℝ) (h0 : 0 < γ) (h1 : γ ≤ 1)
    (X : CMatrix (Fin 2)) :
    complementInverse γ
      ((channel (1 - γ) (sub_nonneg.mpr h1) (by linarith)).map X) = X := by
  rw [channel_apply]
  have hγ : (γ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h0
  have hs : (Real.sqrt γ : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr h0)
  have hg : 1 - (1 - γ) = γ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complementInverse, hg]
  all_goals push_cast
  all_goals field_simp
  all_goals ring

theorem complement_bijective (γ : ℝ) (h0 : 0 < γ) (h1 : γ ≤ 1) :
    Function.Bijective (channel (1 - γ) (sub_nonneg.mpr h1) (by linarith)).map :=
  ⟨Function.LeftInverse.injective (complement_inverse_left γ h0 h1),
    Function.RightInverse.surjective (complement_inverse_right γ h0 h1)⟩

theorem shadow_adjoint_inverse (γ : ℝ) (h0 : 0 < γ) (h1 : γ ≤ 1) :
    MatrixSpace.hsAdjoint (shadow γ) = (channel γ h0.le h1).map.comp (complementInverse γ) := by
  ext X i j
  have h := (shadow_unbiased γ h0 h1).reconstruct (complementInverse γ X)
  rw [complement_inverse_right γ h0 h1] at h
  exact congrFun (congrFun h i) j

theorem shadow_mean_reference (γ : ℝ) (h0 : 0 < γ) (h1 : γ ≤ 1)
    (r : Type) [Fintype r] [DecidableEq r]
    (X Y : CMatrix (r × Fin 2)) :
    (amp r (channel γ h0.le h1).map X * Y).trace =
      (amp r (channel (1 - γ) (sub_nonneg.mpr h1) (by linarith)).map X *
        amp r (shadow γ) Y).trace :=
  (shadow_unbiased γ h0 h1).amp_mean_eq X Y

theorem quantumCapacity_pos (γ : ℝ) (h0 : 0 < γ) (hhalf : γ < 1 / 2)
    (coding : External.QuantumCoding (channel γ h0.le (by linarith))) :
    0 < (channel γ h0.le (by linarith)).quantumCapacity := by
  let N := channel γ h0.le (by linarith : γ ≤ 1)
  let ρ := State.maximallyMixed (Fin 2)
  have hp : 0 < N.coherentInformationFor ρ.canonicalPurification := by
    rw [(complementary γ h0.le (by linarith)).coherentInformationFor_eq,
      show ρ.canonicalPurification.state.marginalB = ρ from
        State.ext ρ.canonicalPurification_purifies]
    exact coherent_pos γ h0 hhalf
  have hS : Simulates N (N.tensorPower 1) :=
    simulation_discard_padding N Channel.unit PUnit.unit
  obtain ⟨ψ, hψ⟩ := hS.exists_positive_input ρ.canonicalPurification hp
  exact quantumCapacity_pos_of_block N coding 1 (by norm_num) ψ hψ

end QuanIncapacity.AmplitudeDamping
