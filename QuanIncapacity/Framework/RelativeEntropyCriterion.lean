import QuanIncapacity.Framework.BKMCriterion
import QuanIncapacity.Framework.RelativeEntropyIntegral

/-! The faithful relative-entropy consequence of complete observable shadowing. -/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open QIT MeasureTheory QuanIncapacity.MatrixSpace

namespace QuanIncapacity

variable {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Nonempty b]
variable [Fintype e] [DecidableEq e] [Nonempty e]

/-- The manuscript's complete BKM order: normalized faithful base states and
traceless Hermitian tangent vectors, with natural-logarithm metric weights. -/
def CompleteBKMOrder (N : Channel a b) (M : Channel a e)
    (hN : (N.map 1).PosDef) (hM : (M.map 1).PosDef) : Prop :=
  ∀ (r : Type) [Fintype r] [DecidableEq r] [Nonempty r],
    ∀ (τ : State (r × a)) (hτ : τ.matrix.PosDef) (X : CMatrix (r × a)),
      X.IsHermitian → X.trace = 0 →
      BKM.metric (amp_posDef N hN hτ) (amp r N.map X) ≤
        BKM.metric (amp_posDef M hM hτ) (amp r M.map X)

theorem Shadowing.completeBKMOrder (N : Channel a b) (M : Channel a e)
    (J : MatrixMap b e) (h : Shadowing.IsCompleteShadow N.map M.map J)
    (hN : (N.map 1).PosDef) (hM : (M.map 1).PosDef) : CompleteBKMOrder N M hN hM :=
  fun r _ _ _ τ hτ X _ _ ↦ Shadowing.complete_bkm_order N M J h hN hM r τ.matrix X hτ

theorem CompleteBKMOrder.relativeEntropy_le_of_posDef {N : Channel a b} {M : Channel a e}
    {hN : (N.map 1).PosDef} {hM : (M.map 1).PosDef} (h : CompleteBKMOrder N M hN hM)
    (r : Type) [Fintype r] [DecidableEq r] [Nonempty r]
    (ρ σ : State (r × a)) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) :
    (((Channel.idChannel r).prod N).applyState ρ).relativeEntropy
        (((Channel.idChannel r).prod N).applyState σ) ≤
      (((Channel.idChannel r).prod M).applyState ρ).relativeEntropy
        (((Channel.idChannel r).prod M).applyState σ) := by
  let NR := (Channel.idChannel r).prod N
  let MR := (Channel.idChannel r).prod M
  have hNρ : (NR.applyState ρ).matrix.PosDef := amp_posDef N hN hρ
  have hNσ : (NR.applyState σ).matrix.PosDef := amp_posDef N hN hσ
  have hMρ : (MR.applyState ρ).matrix.PosDef := amp_posDef M hM hρ
  have hMσ : (MR.applyState σ).matrix.PosDef := amp_posDef M hM hσ
  rw [BKM.relativeEntropy_eq_integral_of_posDef (NR.applyState ρ) (NR.applyState σ) hNρ hNσ,
    BKM.relativeEntropy_eq_integral_of_posDef (MR.applyState ρ) (MR.applyState σ) hMρ hMσ]
  apply EReal.coe_le_coe_iff.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / Real.log 2)
  have hint {c : Type} [Fintype c] [DecidableEq c] (U V : CMatrix c)
      (hU : U.PosDef) (hV : V.PosDef) :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t) * arithmeticMetric (V + t • (U - V)) (U - V))
        volume 0 1 := by
    have hc := arithmeticMetric_continuousOn
      (σ := fun t : ℝ ↦ V + t • (U - V)) (p := 0) (q := 1) (by fun_prop)
      (fun _ ht ↦ BKM.affine_segment_posDef hU hV ht) (U - V)
    apply ContinuousOn.intervalIntegrable
    simpa [Pi.mul_def, Pi.sub_def] using (continuousOn_const.sub continuousOn_id).mul hc
  apply intervalIntegral.integral_mono_on zero_le_one
    (hint _ _ hNρ hNσ) (hint _ _ hMρ hMσ)
  intro t ht
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht.2)
  let τ : State (r × a) :=
    { matrix := σ.matrix + t • (ρ.matrix - σ.matrix)
      pos := (BKM.affine_segment_posDef hρ hσ ht).posSemidef
      trace_eq_one := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub,
          ρ.trace_eq_one, σ.trace_eq_one]
        simp }
  have hh := h r τ (BKM.affine_segment_posDef hρ hσ ht) (ρ.matrix - σ.matrix)
    (ρ.pos.isHermitian.sub σ.pos.isHermitian)
    (by rw [Matrix.trace_sub, ρ.trace_eq_one, σ.trace_eq_one, sub_self])
  rw [BKM.metric_eq_arithmeticMetric, BKM.metric_eq_arithmeticMetric] at hh
  dsimp only [τ] at hh
  change arithmeticMetric
      (amp r N.map σ.matrix + t • (amp r N.map ρ.matrix - amp r N.map σ.matrix))
      (amp r N.map ρ.matrix - amp r N.map σ.matrix) ≤
    arithmeticMetric
      (amp r M.map σ.matrix + t • (amp r M.map ρ.matrix - amp r M.map σ.matrix))
      (amp r M.map ρ.matrix - amp r M.map σ.matrix)
  simpa only [map_add, map_sub, LinearMap.map_smul_of_tower] using hh

theorem Shadowing.complete_relativeEntropy_order_of_posDef (N : Channel a b) (M : Channel a e)
    (J : MatrixMap b e) (h : Shadowing.IsCompleteShadow N.map M.map J)
    (hN : (N.map 1).PosDef) (hM : (M.map 1).PosDef)
    (r : Type) [Fintype r] [DecidableEq r] [Nonempty r]
    (ρ σ : State (r × a)) (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef) :
    (((Channel.idChannel r).prod N).applyState ρ).relativeEntropy
        (((Channel.idChannel r).prod N).applyState σ) ≤
      (((Channel.idChannel r).prod M).applyState ρ).relativeEntropy
        (((Channel.idChannel r).prod M).applyState σ) :=
  (Shadowing.completeBKMOrder N M J h hN hM).relativeEntropy_le_of_posDef r ρ σ hρ hσ

end QuanIncapacity
