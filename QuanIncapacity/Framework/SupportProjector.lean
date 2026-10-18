import QuanIncapacity.Framework.UnitaryMetric
import QIT.States.Schatten

/-! A zero sandwiched operator remains zero when the positive weight is
replaced by its actual spectral support projector, including singular weights. -/

noncomputable section
open QIT Unitary QuanIncapacity.MatrixSpace
open scoped Matrix BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false

namespace QuanIncapacity

variable {a : Type} [Fintype a] [DecidableEq a]

def supportProjector (C : CMatrix a) (hC : C.PosSemidef) : CMatrix a :=
  psdInvSqrt C hC.isHermitian * C * psdInvSqrt C hC.isHermitian

theorem supportProjector_eq_isometry (C : CMatrix a) (hC : C.PosSemidef) :
    supportProjector C hC = psdSupportIsometry C hC * (psdSupportIsometry C hC).conjTranspose :=
  (psdSupportIsometry_mul_conjTranspose_eq_supportProjector C hC).symm

theorem psdInvSqrt_commute (C : CMatrix a) (hC : C.PosSemidef) :
    psdInvSqrt C hC.isHermitian * C = C * psdInvSqrt C hC.isHermitian := by
  let U := hC.isHermitian.eigenvectorUnitary
  let D := Matrix.diagonal (fun i ↦ (hC.isHermitian.eigenvalues i : ℂ))
  let R := Matrix.diagonal (fun i ↦ if 0 < hC.isHermitian.eigenvalues i
    then (Real.rpow (hC.isHermitian.eigenvalues i) (-(1 : ℝ) / 2) : ℂ) else 0)
  have hspec : C = conjugation U D := hC.isHermitian.spectral_theorem
  have hR : psdInvSqrt C hC.isHermitian = conjugation U R := rfl
  have hcomm : R * D = D * R := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  calc
    _ = conjugation U R * conjugation U D := congrArg₂ (· * ·) hR hspec
    _ = conjugation U (R * D) := (conjugation_mul U R D).symm
    _ = conjugation U (D * R) := congrArg (conjugation U) hcomm
    _ = _ := (conjugation_mul U D R).trans (congrArg₂ (· * ·) hspec.symm hR.symm)

theorem supportProjector_sandwich_zero (C : CMatrix a) (hC : C.PosSemidef)
    (Z : CMatrix a) (h : C * Z * C = 0) :
    supportProjector C hC * Z * supportProjector C hC = 0 := by
  let R := psdInvSqrt C hC.isHermitian
  have hc : R * C = C * R := psdInvSqrt_commute C hC
  have hl : supportProjector C hC = R ^ 2 * C := by
    change R * C * R = _
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← pow_two]
  have hr : supportProjector C hC = C * R ^ 2 := by
    change R * C * R = _
    rw [hc, Matrix.mul_assoc, pow_two]
  calc
    _ = (R ^ 2 * C) * Z * supportProjector C hC :=
      congrArg (fun P ↦ P * Z * supportProjector C hC) hl
    _ = (R ^ 2 * C) * Z * (C * R ^ 2) := congrArg (fun P ↦ (R ^ 2 * C) * Z * P) hr
    _ = R ^ 2 * (C * Z * C) * R ^ 2 := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

end QuanIncapacity
