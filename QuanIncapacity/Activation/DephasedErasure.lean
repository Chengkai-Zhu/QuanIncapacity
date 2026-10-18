import QuanIncapacity.Activation.ExcitationTensor
import QuanIncapacity.Framework.FlagDecoder

/-! The complete channel equation for arbitrary single-excitation dimension.
The decoder acts on the whole qubit output space and is CPTP. -/

noncomputable section
open QIT
open scoped BigOperators Matrix

namespace QuanIncapacity

namespace DephasedErasure

variable {a : Type} [Fintype a] [DecidableEq a]

/-- Surviving block `q (η X + (1-η) Δ(X))` and a separate erasure flag. -/
def matrix (q η : ℝ) (X : CMatrix a) : CMatrix (Option a)
  | some i, some j => (q : ℂ) * ((η : ℂ) * X i j + (1 - (η : ℂ)) * if i = j then X i i else 0)
  | none, none => (1 - (q : ℂ)) * X.trace
  | _, _ => 0

def map (q η : ℝ) : MatrixMap a (Option a) where
  toFun := matrix q η
  map_add' X Y := by
    ext i j
    cases i <;> cases j <;> simp [matrix, Matrix.trace_add, mul_add]
    split_ifs <;> simp_all [mul_add] <;> ring
  map_smul' z X := by
    ext i j
    cases i <;> cases j <;> simp [matrix, Matrix.trace_smul, Matrix.smul_apply, smul_eq_mul]
    · ring
    · split_ifs <;> simp_all <;> ring

theorem map_diagonal (q η : ℝ) (i : a) :
    map q η (Matrix.single i i 1) =
      (1 - (q : ℂ)) • Matrix.single none none 1 +
      (q : ℂ) • Matrix.single (some i) (some i) 1 := by
  ext x y
  cases x <;> cases y <;>
    simp [map, matrix, Matrix.single_apply, Matrix.trace, Matrix.diag, Matrix.smul_apply]
  split_ifs <;> simp_all <;> try aesop <;> ring

theorem map_off_diagonal (q η : ℝ) (i j : a) (hij : i ≠ j) :
    map q η (Matrix.single i j 1) =
      ((q : ℂ) * (η : ℂ)) • Matrix.single (some i) (some j) 1 := by
  have hz : ∀ x : a, ¬ (i = x ∧ j = x) := by intro x hx; exact hij (hx.1.trans hx.2.symm)
  ext x y
  cases x <;> cases y <;>
    simp [map, matrix, Matrix.single_apply, Matrix.trace, Matrix.diag, Matrix.smul_apply, hz]

end DephasedErasure

namespace Excitation

def physicalChannel (n : ℕ) : Channel (Fin n) (QIT.TensorPower (Fin 2) n) :=
  (restrictedQubitChannel.tensorPower n).comp (Channel.ofReferenceIsometry (encoder n))

theorem physicalChannel_single (n : ℕ) (i j : Fin n) :
    (physicalChannel n).map (Matrix.single i j 1) =
      power n (Matrix.single (location n i) (location n j) 1) := by
  change power n (MatrixMap.ofReferenceIsometry (encoder n) (Matrix.single i j 1)) = _
  rw [encoder, MatrixMap.ofReferenceIsometry_ofInjective_single]

/-- No amplitude leaves the span of the excitation basis and the vacuum.
This entrywise statement applies to every complex input, hence in particular
to all density states and their off-diagonal coherences. -/
theorem physicalChannel_supported (n : ℕ) (X : CMatrix (Fin n))
    (x y : QIT.TensorPower (Fin 2) n)
    (hout : (x ≠ vacuum n ∧ ∀ i, x ≠ location n i) ∨
      (y ≠ vacuum n ∧ ∀ i, y ≠ location n i)) : (physicalChannel n).map X x y = 0 := by
  rw [MatrixMap.map_eq_sum_single (physicalChannel n).map X]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [physicalChannel_single]
  have hz : power n (Matrix.single (location n i) (location n j) 1) x y = 0 := by
    by_cases hij : i = j
    · subst j
      rw [diagonal]
      rcases hout with hx | hy
      · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, hx.1.symm, (hx.2 i).symm]
      · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, hy.1.symm, (hy.2 i).symm]
    · rw [off_diagonal n i j hij]
      rcases hout with hx | hy
      · simp [Matrix.smul_apply, Matrix.single_apply, (hx.2 i).symm]
      · simp [Matrix.smul_apply, Matrix.single_apply, (hy.2 j).symm]
  rw [hz, mul_zero]

def encodedChannel (n : ℕ) : Channel (Fin n) (Option (Fin n)) :=
  ((FlagDecoder.channel (location n)).comp (restrictedQubitChannel.tensorPower n)).comp
    (Channel.ofReferenceIsometry (encoder n))

theorem encoded_diagonal (n : ℕ) (i : Fin n) :
    (encodedChannel n).map (Matrix.single i i 1) =
      (3 / 4 : ℂ) • Matrix.single none none 1 +
      (1 / 4 : ℂ) • Matrix.single (some i) (some i) 1 := by
  change (FlagDecoder.channel (location n)).map
    (power n (MatrixMap.ofReferenceIsometry (encoder n) (Matrix.single i i 1))) = _
  rw [encoder, MatrixMap.ofReferenceIsometry_ofInjective_single, diagonal,
    map_add, map_smul, map_smul, FlagDecoder.map_code _ (location_injective n)]
  rw [FlagDecoder.map_outside _ _ (by rintro ⟨j, hj⟩; exact location_ne_vacuum n j hj)]

theorem encoded_off_diagonal (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (encodedChannel n).map (Matrix.single i j 1) =
      (1 / 16 : ℂ) • Matrix.single (some i) (some j) 1 := by
  change (FlagDecoder.channel (location n)).map
    (power n (MatrixMap.ofReferenceIsometry (encoder n) (Matrix.single i j 1))) = _
  rw [encoder, MatrixMap.ofReferenceIsometry_ofInjective_single, off_diagonal n i j hij,
    map_smul, FlagDecoder.map_code _ (location_injective n)]

/-- Equality of actual CPTP encoding, all `n` channel uses, and actual CPTP
decoding, for every complex input matrix. In particular this covers `n = 1`. -/
theorem encodedChannel_map (n : ℕ) :
    (encodedChannel n).map = DephasedErasure.map (a := Fin n) (1 / 4) (1 / 4) := by
  have hs (i j : Fin n) : (encodedChannel n).map (Matrix.single i j 1) =
      DephasedErasure.map (a := Fin n) (1 / 4) (1 / 4) (Matrix.single i j 1) := by
    by_cases hij : i = j
    · subst j
      rw [encoded_diagonal, DephasedErasure.map_diagonal]
      norm_num
    · rw [encoded_off_diagonal n i j hij, DephasedErasure.map_off_diagonal _ _ i j hij]
      norm_num
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single (encodedChannel n).map X,
    MatrixMap.map_eq_sum_single (DephasedErasure.map (1 / 4) (1 / 4)) X]
  simp only [hs]

theorem encodedChannel_apply (n : ℕ) (X : CMatrix (Fin n)) :
    (encodedChannel n).map X = DephasedErasure.matrix (1 / 4) (1 / 4) X := by
  rw [encodedChannel_map]
  rfl

end Excitation
end QuanIncapacity
