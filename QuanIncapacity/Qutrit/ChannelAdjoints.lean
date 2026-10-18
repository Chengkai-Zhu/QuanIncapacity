import QuanIncapacity.Qutrit.ComponentIdentities
import QuanIncapacity.Framework.Adjoint

/-! Explicit qutrit formulas connected to the general Hilbert--Schmidt adjoint. -/
noncomputable section
open QIT QuanIncapacity.MatrixSpace
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity

theorem lambda_hsAdjoint : hsAdjoint Λ_map = Λ_map := by
  apply LinearMap.ext
  intro X
  ext i j
  rw [hsAdjoint_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Λ_map, Matrix.single_apply, Matrix.trace, Matrix.diag, Matrix.transpose_apply,
      Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul,
      Fin.sum_univ_succ, map_ofNat]
  all_goals ring

theorem complement_hsAdjoint (Z : CMatrix (Fin 4)) :
    hsAdjoint Λc_map Z = complementAdjointEntries Z := by
  have h : hsAdjoint Λc_map Z = MatrixMap.krausAdjoint Ec Z := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    have hp := hsAdjoint_pairing Λc_map X.conjTranspose Z
    have ha : Λc_map X.conjTranspose = (Λc_map X).conjTranspose := by
      rw [Λc_map_eq_ofKraus]
      simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [ha, Matrix.conjTranspose_conjTranspose] at hp
    have hd := MatrixMap.ofKraus_trace_duality Ec X Z
    rw [← Λc_map_eq_ofKraus] at hd
    simpa only [Matrix.conjTranspose_conjTranspose] using hp.symm.trans hd
  rw [h]
  exact complement_adjoint_block Z

end QuanIncapacity
