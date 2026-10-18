import QIT.Channels.Stinespring
import QIT.States.Purification.Uhlmann

/-!
# Certified complementary channels

Both marginals must come from the same isometry, including its entire
environment. Equality of dimensions or two independent CPTP certificates is
not a complementarity certificate.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT

namespace QuanIncapacity

variable {a b e : Type*} [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

def ComplementaryChannels (N : Channel a b) (M : Channel a e) : Prop :=
  ∃ V : ReferenceIsometry a (b × e), V.outputChannel = N ∧ V.complementaryChannel = M

theorem channel_eq_of_map_eq (N M : Channel a b) (h : N.map = M.map) : N = M := by
  cases N
  cases M
  cases h
  rfl

namespace Stinespring

/-- The full complementary output of any finite trace-preserving Kraus family. -/
theorem complementary_kraus_map (K : e → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K)) (X : CMatrix a)
    (i j : e) :
    (MatrixMap.krausStinespringIsometry K hTP).complementaryChannel.map X i j =
      (K i * X * (K j).conjTranspose).trace := by
  rw [ReferenceIsometry.complementaryChannel_map]
  simp only [MatrixMap.krausStinespringIsometry, partialTraceA, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag_apply]
  rfl

end Stinespring
end QuanIncapacity
