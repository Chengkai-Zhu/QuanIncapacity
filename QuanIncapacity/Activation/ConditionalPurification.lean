import QuanIncapacity.Framework.HolevoRelativeEntropy
import QIT.States.Purification.Conditioning

/-! Purifications with the manuscript's exact auxiliary dimension:
the sum of the ranks of the signal states. Distinct messages occupy disjoint
computational subspaces. -/

noncomputable section
open QIT
open scoped BigOperators ComplexOrder MatrixOrder

namespace QuanIncapacity.Activation

variable {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]

theorem card_psdSupportIndex_eq_rank (ρ : State a) :
    Fintype.card (psdSupportIndex ρ.matrix ρ.pos) = ρ.matrix.rank := by
  let V := psdSupportIsometry ρ.matrix ρ.pos
  let D := psdSupportCompress ρ.matrix ρ.pos ρ.matrix
  have hrec : V * D * V.conjTranspose = ρ.matrix :=
    psdSupportCompress_reconstruct_of_supports ρ.pos ρ.pos (Matrix.Supports.refl _)
  have hr : D.rank = ρ.matrix.rank := by
    apply le_antisymm
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · calc
        ρ.matrix.rank = (V * D * V.conjTranspose).rank := congrArg Matrix.rank hrec.symm
        _ ≤ D.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [← hr]
  exact (Matrix.rank_of_isUnit D (psdSupportCompress_self_posDef ρ.matrix ρ.pos).isUnit).symm

def supportPurification (ρ : State a) : PureVector (psdSupportIndex ρ.matrix ρ.pos × a) :=
  (State.psdSupportReferenceIsometry ρ.matrix ρ.pos).applyPureVectorRight
    (psdSupportCompressedState ρ ρ.pos (Matrix.Supports.refl _)).canonicalPurification

theorem supportPurification_purifies (ρ : State a) :
    (supportPurification ρ).Purifies ρ := by
  rw [PureVector.purifies_iff]
  change partialTraceA (supportPurification ρ).state.matrix = ρ.matrix
  rw [supportPurification, ReferenceIsometry.rankOne_applyPureVectorRight,
    ReferenceIsometry.partialTraceA_applyMatrixRight]
  rw [(psdSupportCompressedState ρ ρ.pos (Matrix.Supports.refl _)).canonicalPurification_purifies]
  exact psdSupportCompress_reconstruct_of_supports ρ.pos ρ.pos (Matrix.Supports.refl _)

abbrev SignalRef (E : Ensemble ι a) (i : ι) := psdSupportIndex (E.states i).matrix (E.states i).pos

abbrev Auxiliary (E : Ensemble ι a) := (i : ι) × SignalRef E i

theorem auxiliary_card (E : Ensemble ι a) :
    Fintype.card (Auxiliary E) = ∑ i, (E.states i).matrix.rank := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun i _ ↦ card_psdSupportIndex_eq_rank (E.states i))

def signalEmbedding (E : Ensemble ι a) (i : ι) : ReferenceIsometry (SignalRef E i) (Auxiliary E) :=
  ReferenceIsometry.ofInjective (Sigma.mk i) (fun _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2)

def conditionalVector (E : Ensemble ι a) (i : ι) : PureVector (Auxiliary E × a) :=
  (signalEmbedding E i).applyPureVector (supportPurification (E.states i))

theorem conditionalVector_purifies (E : Ensemble ι a) (i : ι) :
    (conditionalVector E i).Purifies (E.states i) :=
  (signalEmbedding E i).applyPureVector_purifies (supportPurification_purifies (E.states i))

theorem conditionalVector_supported (E : Ensemble ι a) (i : ι) (c : Auxiliary E) (x : a)
    (h : c.1 ≠ i) : (conditionalVector E i).amp (c, x) = 0 := by
  change ∑ k : SignalRef E i, (if c = Sigma.mk i k then (1 : ℂ) else 0) *
    (supportPurification (E.states i)).amp (k, x) = 0
  apply Finset.sum_eq_zero
  intro k _
  have hn : c ≠ Sigma.mk i k := fun hc ↦ h (congrArg Sigma.fst hc)
  simp [hn]

/-- Orthogonality holds entrywise on the auxiliary basis, which is stronger
than orthogonality of the total vectors and survives tracing out that basis. -/
theorem conditionalVector_cross_zero (E : Ensemble ι a) (i j : ι) (hij : i ≠ j)
    (c : Auxiliary E) (x y : a) :
    (conditionalVector E i).amp (c, x) * star ((conditionalVector E j).amp (c, y)) = 0 := by
  by_cases hi : c.1 = i
  · rw [conditionalVector_supported E j c y (fun hj ↦ hij (hi.symm.trans hj))]
    simp
  · rw [conditionalVector_supported E i c x hi, zero_mul]

end QuanIncapacity.Activation
