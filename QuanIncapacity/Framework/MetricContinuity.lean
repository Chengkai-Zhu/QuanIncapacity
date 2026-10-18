import QuanIncapacity.Framework.LogDerivative

/-! Continuity of the integrated inverse metric on faithful matrix paths. -/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology
open QIT MeasureTheory Filter

namespace QuanIncapacity

theorem continuousOn_integral_unit_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ} (F : ℝ × ℝ → E)
    (hF : ContinuousOn F (Set.Icc p q ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun u : ℝ ↦ ∫ t : ℝ in 0..1, F (u, t)) (Set.Icc p q) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF
  have hmeas : ∀ u ∈ Set.Icc p q,
      AEStronglyMeasurable (fun t : ℝ ↦ F (u, t)) (volume.restrict (Set.Ioc 0 1)) := by
    intro u hu
    have hc : ContinuousOn (fun t : ℝ ↦ F (u, t)) (Set.Icc 0 1) :=
      hF.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht ↦ ⟨hu, ht⟩)
    have hi : IntervalIntegrable (fun t : ℝ ↦ F (u, t)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      simpa using hc
    exact hi.1.aestronglyMeasurable
  have hbound : ∀ u ∈ Set.Icc p q,
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), ‖F (u, t)‖ ≤ C := by
    intro u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hC (u, t) ⟨hu, ⟨ht.1.le, ht.2⟩⟩
  have hcont : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ContinuousOn (fun u : ℝ ↦ F (u, t)) (Set.Icc p q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hF.comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ hu ↦ ⟨hu, ⟨ht.1.le, ht.2⟩⟩)
  simpa only [intervalIntegral.integral_of_le zero_le_one] using
    (continuousOn_of_dominated hmeas hbound (by exact integrable_const C) hcont)

namespace MatrixSpace

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem arithmeticMetric_continuousOn {σ : ℝ → CMatrix a} {p q : ℝ}
    (hσ : ContinuousOn σ (Set.Icc p q))
    (hpos : ∀ u ∈ Set.Icc p q, (σ u).PosDef) (X : CMatrix a) :
    ContinuousOn (fun u : ℝ ↦ arithmeticMetric (σ u) X) (Set.Icc p q) := by
  let rect := Set.Icc p q ×ˢ Set.Icc (0 : ℝ) 1
  have hs : ContinuousOn (fun z : ℝ × ℝ ↦ σ z.1) rect :=
    hσ.comp continuousOn_fst (fun _ hz ↦ hz.1)
  have hl : Continuous (left : CMatrix a → CMatrix (a × a)) := by
    apply continuous_matrix
    intro i j
    simp only [left, Matrix.kronecker, Matrix.kroneckerMap_apply]
    fun_prop
  have hr : Continuous (right : CMatrix a → CMatrix (a × a)) := by
    apply continuous_matrix
    intro i j
    simp only [right, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    fun_prop
  have hA : ContinuousOn (fun z : ℝ × ℝ ↦ arithmetic (σ z.1) z.2) rect := by
    exact ((continuousOn_const.sub continuousOn_snd).smul (hl.comp_continuousOn hs)).add
      (continuousOn_snd.smul (hr.comp_continuousOn hs))
  have hi : ContinuousOn (fun z : ℝ × ℝ ↦ (arithmetic (σ z.1) z.2)⁻¹) rect := by
    intro z hz
    have hu := (arithmetic_posDef (hpos z.1 hz.1) hz.2.1 hz.2.2).isUnit
    have hInv : ContinuousAt Ring.inverse (arithmetic (σ z.1) z.2) := by
      simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using
      hInv.comp_continuousWithinAt (f := fun z : ℝ × ℝ ↦ arithmetic (σ z.1) z.2) (hA z hz)
  have hquad : Continuous (fun A : CMatrix (a × a) ↦ quadratic A (vec X)) := by
    unfold quadratic Matrix.mulVec dotProduct
    fun_prop
  exact continuousOn_integral_unit_interval _ (hquad.comp_continuousOn hi)

end MatrixSpace
end QuanIncapacity
