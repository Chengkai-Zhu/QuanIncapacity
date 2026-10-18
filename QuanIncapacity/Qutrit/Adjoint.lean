import QuanIncapacity.Qutrit.Defect
import QuanIncapacity.Framework.MatrixSpace

/-! The manuscript's explicit adjoint is the actual Hilbert–Schmidt adjoint. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT QuanIncapacity.MatrixSpace

namespace QuanIncapacity

theorem shadow_adjoint_pairing (X : CMatrix (Fin 3)) (Y : CMatrix (Fin 4)) :
    ((𝒥_map X).conjTranspose * Y).trace = (X.conjTranspose * 𝒥adj Y).trace := by
  simp [𝒥adj, shadowAdjointEntries, shadowEntries, avec, Matrix.trace,
    Matrix.mul_apply, Matrix.conjTranspose, A, levN, fin3ToFin4, fin4ToFin3]
  change Fin 3 → Fin 3 → ℂ at X
  change Fin 4 → Fin 4 → ℂ at Y
  norm_num [map_ofNat]
  ring

theorem shadow_adjoint_eq_hsAdjoint : 𝒥adj = hsAdjoint 𝒥_map := by
  apply LinearMap.ext
  intro Y
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  calc
    (X * 𝒥adj Y).trace = ((𝒥_map X.conjTranspose).conjTranspose * Y).trace := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        (shadow_adjoint_pairing X.conjTranspose Y).symm
    _ = (X * hsAdjoint 𝒥_map Y).trace := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        hsAdjoint_pairing 𝒥_map X.conjTranspose Y

end QuanIncapacity
