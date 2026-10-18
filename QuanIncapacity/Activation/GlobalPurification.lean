import QuanIncapacity.Activation.ConditionalPurification
import QuanIncapacity.Activation.EntropyBounds

/-! The reference in this construction is quantum. It becomes classical only
after the orthogonal auxiliary register is discarded. -/

noncomputable section
open QIT
open scoped BigOperators NNReal

namespace QuanIncapacity.Activation

variable {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]

theorem sqrt_weight_sq (E : Ensemble ι a) (i : ι) :
    (Real.sqrt (E.probs i : ℝ) : ℂ) * (Real.sqrt (E.probs i : ℝ) : ℂ) = (E.probs i : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (E.prob_nonneg i)]


def globalPurificationRaw (E : Ensemble ι a) : PureVector (ι × (Auxiliary E × a)) where
  amp z := (Real.sqrt (E.probs z.1 : ℝ) : ℂ) * (conditionalVector E z.1).amp z.2
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace]
    simp only [dotProduct, Fintype.sum_prod_type]
    have hnorm (i : ι) : ∑ c, ∑ x, (conditionalVector E i).amp (c, x) *
        star ((conditionalVector E i).amp (c, x)) = 1 := by
      simpa only [rankOneMatrix_trace, dotProduct, Fintype.sum_prod_type] using
        (conditionalVector E i).trace_rankOne_eq_one
    calc
      _ = ∑ i, ((Real.sqrt (E.probs i : ℝ) : ℂ) * (Real.sqrt (E.probs i : ℝ) : ℂ)) *
          (∑ c, ∑ x, (conditionalVector E i).amp (c, x) *
            star ((conditionalVector E i).amp (c, x))) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Finset.mul_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = ∑ i, (E.probs i : ℂ) := by simp only [hnorm, sqrt_weight_sq, mul_one]
      _ = 1 := by exact_mod_cast E.weights_sum

def globalPurification (E : Ensemble ι a) : PureVector (ι × (a × Auxiliary E)) :=
  (globalPurificationRaw E).reindex (Equiv.prodCongr (Equiv.refl ι) (Equiv.prodComm _ _))

theorem globalPurification_amp (E : Ensemble ι a) (i : ι) (x : a) (c : Auxiliary E) :
    (globalPurification E).amp (i, (x, c)) =
      (Real.sqrt (E.probs i : ℝ) : ℂ) * (conditionalVector E i).amp (c, x) := rfl

theorem globalPurification_supported (E : Ensemble ι a) (i : ι) (x : a) (c : Auxiliary E)
    (hi : i ≠ c.1) : (globalPurification E).amp (i, (x, c)) = 0 := by
  rw [globalPurification_amp, conditionalVector_supported E i c x (Ne.symm hi), mul_zero]

def dropAuxiliary {r b c : Type} [Fintype r] [DecidableEq r]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (ρ : State (r × (b × c))) : State (r × b) :=
  (ρ.reindex (Equiv.prodAssoc r b c).symm).marginalA

theorem dropAuxiliary_matrix {r b c : Type} [Fintype r] [DecidableEq r]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (ρ : State (r × (b × c))) (x y : r) (u v : b) :
    (dropAuxiliary ρ).matrix (x, u) (y, v) = ∑ k, ρ.matrix (x, (u, k)) (y, (v, k)) := rfl

/-- Discarding the auxiliary register gives exactly the original cq ensemble,
including its zero-probability entries. -/
theorem globalPurification_dropAuxiliary (E : Ensemble ι a) :
    dropAuxiliary (globalPurification E).state = E.cqState := by
  apply State.ext
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [dropAuxiliary_matrix]
  simp only [PureVector.state_matrix_apply, globalPurification_amp, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  by_cases hij : i = j
  · subst j
    have hφ := congrFun (congrFun (conditionalVector_purifies E i) x) y
    change (∑ c, (conditionalVector E i).amp (c, x) *
      star ((conditionalVector E i).amp (c, y))) = (E.states i).matrix x y at hφ
    have hc := congrFun (congrFun (QIT.Classical.cqState_block_self E i) x) y
    change (E.cqState).matrix (i, x) (i, y) = _ at hc
    rw [hc]
    change _ = (E.probs i : ℂ) * (E.states i).matrix x y
    rw [← hφ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    change _ = (E.probs i : ℂ) *
      ((conditionalVector E i).amp (c, x) * star ((conditionalVector E i).amp (c, y)))
    rw [← sqrt_weight_sq E i]
    simp only [Complex.star_def]
    ring
  · have hc := congrFun (congrFun (QIT.Classical.cqState_block_ne E hij) x) y
    change (E.cqState).matrix (i, x) (j, y) = 0 at hc
    rw [hc]
    apply Finset.sum_eq_zero
    intro c _
    have hz := conditionalVector_cross_zero E i j hij c x y
    calc
      _ = ((Real.sqrt (E.probs i : ℝ) : ℂ) * (Real.sqrt (E.probs j : ℝ) : ℂ)) *
          ((conditionalVector E i).amp (c, x) * star ((conditionalVector E j).amp (c, y))) := by simp only [Complex.star_def]; ring
      _ = 0 := by rw [hz, mul_zero]

end QuanIncapacity.Activation
