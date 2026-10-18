import QuanIncapacity.Framework.ChannelPair

/-! A CPTP decoder for an arbitrary subset of an orthonormal basis.
It preserves the entire code block and sends its orthogonal complement to
one erasure flag; the Stinespring environment records which outside basis
vector was discarded. -/

noncomputable section
open QIT
open scoped BigOperators Matrix

namespace QuanIncapacity.FlagDecoder

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem partialTraceB_single_same (i j : a) (k : b) :
    partialTraceB (Matrix.single (i, k) (j, k) (1 : ℂ)) = Matrix.single i j 1 := by
  rw [single_prod_eq_kronecker_single, partialTraceB_kronecker]
  simp [Matrix.trace, Matrix.diag, Matrix.single, matrixScale]
  ext x y
  exact one_mul _

def embedding (v : a → b) (x : b) : Option a × Option b :=
  if h : ∃ i, v i = x then (some h.choose, none) else (none, some x)

theorem embedding_code (v : a → b) (hv : Function.Injective v) (i : a) :
    embedding v (v i) = (some i, none) := by
  have h : ∃ j, v j = v i := ⟨i, rfl⟩
  simp only [embedding, dif_pos h]
  rw [hv h.choose_spec]

theorem embedding_outside (v : a → b) (x : b) (hx : ¬ ∃ i, v i = x) :
    embedding v x = (none, some x) := by simp only [embedding, dif_neg hx]

theorem embedding_injective (v : a → b) : Function.Injective (embedding v) := by
  intro x y hh
  by_cases hx : ∃ i, v i = x <;> by_cases hy : ∃ i, v i = y
  · simp only [embedding, dif_pos hx, dif_pos hy, Prod.mk.injEq,
      Option.some.injEq, and_true] at hh
    exact hx.choose_spec.symm.trans ((congrArg v hh).trans hy.choose_spec)
  · simp [embedding, hx, hy] at hh
  · simp [embedding, hx, hy] at hh
  · simpa [embedding, hx, hy] using hh

def isometry (v : a → b) : ReferenceIsometry b (Option a × Option b) :=
  ReferenceIsometry.ofInjective (embedding v) (embedding_injective v)

def channel (v : a → b) : Channel b (Option a) := (isometry v).outputChannel

theorem map_single (v : a → b) (x y : b) :
    (channel v).map (Matrix.single x y 1) =
      partialTraceB (Matrix.single (embedding v x) (embedding v y) (1 : ℂ)) := by
  change partialTraceB (MatrixMap.ofReferenceIsometry (isometry v) (Matrix.single x y 1)) = _
  rw [isometry, MatrixMap.ofReferenceIsometry_ofInjective_single]

theorem map_code (v : a → b) (hv : Function.Injective v) (i j : a) :
    (channel v).map (Matrix.single (v i) (v j) 1) = Matrix.single (some i) (some j) 1 := by
  rw [map_single, embedding_code v hv, embedding_code v hv]
  exact partialTraceB_single_same _ _ _

theorem map_outside (v : a → b) (x : b) (hx : ¬ ∃ i, v i = x) :
    (channel v).map (Matrix.single x x 1) = Matrix.single none none 1 := by
  rw [map_single, embedding_outside v x hx]
  exact partialTraceB_single_same _ _ _

end QuanIncapacity.FlagDecoder
