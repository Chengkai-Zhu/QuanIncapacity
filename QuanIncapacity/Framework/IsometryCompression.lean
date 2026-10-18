import QuanIncapacity.Framework.CompleteShadowing
import QIT.Channels.Stinespring
import QIT.Information.Entropy.RelativeEntropyDPI

/-! Observable compression preserves means and decreases variance. -/

noncomputable section
open QIT
open scoped ComplexOrder MatrixOrder Matrix

namespace QuanIncapacity

variable {a b : Type} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

namespace IsometryCompression

def map (V : ReferenceIsometry a b) : MatrixMap b a :=
  MatrixMap.ofKraus (fun _ : Unit ↦ V.matrix.conjTranspose)

theorem map_apply (V : ReferenceIsometry a b) (X : CMatrix b) :
    map V X = V.matrix.conjTranspose * X * V.matrix := by
  simp [map, MatrixMap.ofKraus]

theorem trace_pairing (V : ReferenceIsometry a b) (ρ : CMatrix a) (T : CMatrix b) :
    (V.matrix * ρ * V.matrix.conjTranspose * T).trace = (ρ * map V T).trace := by
  rw [map_apply]
  calc
    _ = ((V.matrix * ρ) * (V.matrix.conjTranspose * T)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((V.matrix.conjTranspose * T) * V.matrix * ρ).trace := by
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = (ρ * (V.matrix.conjTranspose * T) * V.matrix).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem map_image (V : ReferenceIsometry a b) (X : CMatrix a) :
    map V (V.matrix * X * V.matrix.conjTranspose) = X := by
  rw [map_apply]
  calc
    _ = (V.matrix.conjTranspose * V.matrix) * X *
      (V.matrix.conjTranspose * V.matrix) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [V.isometry]; simp

theorem variance_gap (V : ReferenceIsometry a b) (ρ : CMatrix a) (T : CMatrix b) :
    Shadowing.variance (V.matrix * ρ * V.matrix.conjTranspose) T -
      Shadowing.variance ρ (map V T) =
      (ρ * (V.matrix.conjTranspose * T * (1 - V.imageProjector) * T * V.matrix)).trace.re := by
  have hsecond : (V.matrix * ρ * V.matrix.conjTranspose * T * T).trace =
      (ρ * map V (T * T)).trace := by
    rw [Matrix.mul_assoc _ T T]
    exact trace_pairing V ρ (T * T)
  have hdiff : map V (T * T) - map V T * map V T =
      V.matrix.conjTranspose * T * (1 - V.imageProjector) * T * V.matrix := by
    simp only [map_apply, ReferenceIsometry.imageProjector, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  have htrace := congrArg (fun X : CMatrix a ↦ (ρ * X).trace.re) hdiff
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at htrace
  unfold Shadowing.variance
  rw [hsecond, trace_pairing]
  rw [Matrix.mul_assoc ρ (map V T) (map V T)]
  linarith

theorem variance_le (V : ReferenceIsometry a b) {ρ : CMatrix a} (hρ : ρ.PosSemidef)
    {T : CMatrix b} (hT : T.IsHermitian) :
    Shadowing.variance ρ (map V T) ≤
      Shadowing.variance (V.matrix * ρ * V.matrix.conjTranspose) T := by
  have hp := V.one_sub_imageProjector_posSemidef.conjTranspose_mul_mul_same (T * V.matrix)
  have hp' : (V.matrix.conjTranspose * T * (1 - V.imageProjector) * T * V.matrix).PosSemidef := by
    simpa only [Matrix.conjTranspose_mul, hT.eq, Matrix.mul_assoc] using hp
  have ht := cMatrix_trace_mul_posSemidef_re_nonneg hρ hp'
  rw [← variance_gap V ρ T] at ht
  exact sub_nonneg.mp ht

theorem variance_image (V : ReferenceIsometry a b) (ρ Y : CMatrix a) :
    Shadowing.variance (V.matrix * ρ * V.matrix.conjTranspose)
        (V.matrix * Y * V.matrix.conjTranspose) = Shadowing.variance ρ Y := by
  have hmean := trace_pairing V ρ (V.matrix * Y * V.matrix.conjTranspose)
  rw [map_image] at hmean
  have hsquare : (V.matrix * Y * V.matrix.conjTranspose) *
      (V.matrix * Y * V.matrix.conjTranspose) = V.matrix * (Y * Y) * V.matrix.conjTranspose := by
    calc
      _ = V.matrix * Y * (V.matrix.conjTranspose * V.matrix) * Y * V.matrix.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [V.isometry]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hsecond := trace_pairing V ρ
    ((V.matrix * Y * V.matrix.conjTranspose) * (V.matrix * Y * V.matrix.conjTranspose))
  rw [hsquare, map_image] at hsecond
  unfold Shadowing.variance
  rw [hmean, Matrix.mul_assoc _ (V.matrix * Y * V.matrix.conjTranspose),
    hsquare, hsecond, Matrix.mul_assoc]

end IsometryCompression
end QuanIncapacity
