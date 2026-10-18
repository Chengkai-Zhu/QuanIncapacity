import QuanIncapacity.Framework.LogResolvent
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Differentiation of the matrix logarithm along arbitrary Hermitian directions. -/

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology
open QIT MeasureTheory Filter QuanIncapacity.MatrixSpace

namespace QuanIncapacity.BKM

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- A two-sided, uniform faithful neighborhood along a Hermitian affine path. -/
theorem exists_posDef_affine_radius [Nonempty a] {σ X : CMatrix a}
    (hσ : σ.PosDef) (hX : X.IsHermitian) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ Set.Icc (-ε) ε, (σ + u • X).PosDef := by
  obtain ⟨c, hc, hle⟩ := (CFC.exists_pos_algebraMap_le_iff σ hσ.isHermitian).mpr
    (fun x hx ↦ hσ.isStrictlyPositive.spectrum_pos hx)
  let ε := c / (2 * (‖X‖ + 1))
  have he : 0 < ε := div_pos hc (by positivity)
  refine ⟨ε, he, fun u hu ↦ ?_⟩
  have habs : |u| ≤ ε := abs_le.mpr hu
  have hn : ‖u • X‖ ≤ c / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |u| * ‖X‖ ≤ ε * ‖X‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg X)
      _ ≤ ε * (‖X‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) he.le
      _ = c / 2 := by dsimp [ε]; field_simp
  have hneg : -(‖u • X‖ • (1 : CMatrix a)) ≤ u • X := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.neg_algebraMap_norm_le_self (u • X) ((IsSelfAdjoint.all u).smul hX)
  have hsum : (c - ‖u • X‖) • (1 : CMatrix a) ≤ σ + u • X := by
    simpa only [Algebra.algebraMap_eq_smul_one, sub_smul, sub_eq_add_neg, add_smul,
      neg_smul] using add_le_add hle hneg
  have hlower : (c / 2) • (1 : CMatrix a) ≤ σ + u • X := by
    exact (smul_le_smul_of_nonneg_right (by linarith : c / 2 ≤ c - ‖u • X‖)
      (Matrix.PosSemidef.one.nonneg)).trans hsum
  have hdiff : (σ + u • X - (c / 2) • (1 : CMatrix a)).PosSemidef :=
    Matrix.le_iff.mp hlower
  simpa only [add_sub_cancel] using
    (Matrix.PosDef.one.smul (by positivity : 0 < c / 2)).add_posSemidef hdiff

theorem log_resolvent_integrand_hasDerivAt {σ X : CMatrix a} {u t : ℝ}
    (hunit : IsUnit ((1 - t) • (1 : CMatrix a) + t • (σ + u • X))) :
    HasDerivAt (fun v : ℝ ↦ (σ + v • X - 1) * logResolvent (σ + v • X) t)
      (logResolvent (σ + u • X) t * X * logResolvent (σ + u • X) t) u := by
  let A : ℝ → CMatrix a := fun v ↦ (1 - t) • (1 : CMatrix a) + t • (σ + v • X)
  let C : ℝ → CMatrix a := fun v ↦ σ + v • X - 1
  let R := logResolvent (σ + u • X) t
  have hσX : HasDerivAt (fun v : ℝ ↦ σ + v • X) X u := by
    simpa using ((hasDerivAt_id u).smul_const X).const_add σ
  have hA : HasDerivAt A (t • X) u := by
    exact (hσX.const_smul t).const_add ((1 - t) • (1 : CMatrix a))
  have hC : HasDerivAt C X u := hσX.sub_const 1
  have hInvAt : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (CMatrix a)
        (Ring.inverse (A u)) (Ring.inverse (A u))) (A u) := by
    simpa [A, hunit.unit_spec, Ring.inverse_unit, ← Matrix.nonsing_inv_eq_ringInverse]
      using (hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit)
  have hInv : HasDerivAt (fun v : ℝ ↦ logResolvent (σ + v • X) t)
      (-(R * (t • X) * R)) u := by
    have hh := HasFDerivAt.comp_hasDerivAt (f := A) (x := u) hInvAt hA
    simpa [R, A, logResolvent, Matrix.nonsing_inv_eq_ringInverse,
      ContinuousLinearMap.mulLeftRight_apply, Function.comp_def] using hh
  have hAR : A u * R = 1 := by
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hform : A u = 1 + t • C u := by
    dsimp [A, C]
    module
  have htr : t • (C u * R) = 1 - R := by
    rw [hform, add_mul, Matrix.one_mul, smul_mul_assoc] at hAR
    exact eq_sub_of_add_eq' hAR
  have hder : X * R + C u * (-(R * (t • X) * R)) = R * X * R := by
    calc
      _ = (1 - t • (C u * R)) * X * R := by
        simp only [sub_mul, one_mul, mul_neg, mul_smul_comm, smul_mul_assoc, mul_assoc]
        abel
      _ = R * X * R := by rw [htr]; simp
  exact (hC.mul hInv).congr_deriv hder

/-- A compact-rectangle version of differentiation under the integral. -/
theorem hasDerivAt_integral_compact_rectangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ε : ℝ} (hε : 0 < ε) (F G : ℝ × ℝ → E)
    (hF : ContinuousOn F (Set.Icc (-ε) ε ×ˢ Set.Icc 0 1))
    (hG : ContinuousOn G (Set.Icc (-ε) ε ×ˢ Set.Icc 0 1))
    (hd : ∀ u ∈ Set.Icc (-ε) ε, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ ↦ F (v, t)) (G (u, t)) u) :
    HasDerivAt (fun u : ℝ ↦ ∫ t : ℝ in 0..1, F (u, t))
      (∫ t : ℝ in 0..1, G (0, t)) 0 := by
  have hsection {H : ℝ × ℝ → E}
      (hH : ContinuousOn H (Set.Icc (-ε) ε ×ˢ Set.Icc 0 1))
      {u : ℝ} (hu : u ∈ Set.Icc (-ε) ε) :
      IntervalIntegrable (fun t : ℝ ↦ H (u, t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hH.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht ↦ ⟨hu, ht⟩)
  have hzero : (0 : ℝ) ∈ Set.Icc (-ε) ε := ⟨by linarith, hε.le⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  have hn : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hε
  have hmeas : ∀ᶠ u in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (fun t : ℝ ↦ F (u, t)) (volume.restrict (Set.Ioc 0 1)) := by
    filter_upwards [hn] with u hu
    exact (hsection hF ⟨hu.1.le, hu.2.le⟩).1.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ∀ u ∈ Set.Ioo (-ε) ε, ‖G (u, t)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro u hu
    exact hC (u, t) ⟨⟨hu.1.le, hu.2.le⟩, ⟨ht.1.le, ht.2⟩⟩
  have hdiff : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ∀ u ∈ Set.Ioo (-ε) ε, HasDerivAt (fun v : ℝ ↦ F (v, t)) (G (u, t)) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro u hu
    exact hd u ⟨hu.1.le, hu.2.le⟩ t ⟨ht.1.le, ht.2⟩
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hn hmeas
    (hsection hF hzero).1 (hsection hG hzero).1.aestronglyMeasurable hbound
      (by exact integrable_const C) hdiff).2
  simpa only [intervalIntegral.integral_of_le zero_le_one] using hh

theorem log_hasDerivAt_affine_zero [Nonempty a] {σ X : CMatrix a}
    (hσ : σ.PosDef) (hX : X.IsHermitian) :
    HasDerivAt (fun u : ℝ ↦ CFC.log (σ + u • X)) (inverseKuboMori hσ X) 0 := by
  obtain ⟨ε, hε, hpos⟩ := exists_posDef_affine_radius hσ hX
  let rect := Set.Icc (-ε) ε ×ˢ Set.Icc (0 : ℝ) 1
  let R : ℝ × ℝ → CMatrix a := fun p ↦ logResolvent (σ + p.1 • X) p.2
  let F : ℝ × ℝ → CMatrix a := fun p ↦ (σ + p.1 • X - 1) * R p
  let G : ℝ × ℝ → CMatrix a := fun p ↦ R p * X * R p
  have hR : ContinuousOn R rect := by
    intro p hp
    have hu := (logResolvent_posDef (hpos p.1 hp.1) hp.2).isUnit
    have hi : ContinuousAt Ring.inverse
        ((1 - p.2) • (1 : CMatrix a) + p.2 • (σ + p.1 • X)) := by
      simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
    have hc : Continuous (fun p : ℝ × ℝ ↦
        (1 - p.2) • (1 : CMatrix a) + p.2 • (σ + p.1 • X)) := by fun_prop
    change ContinuousWithinAt (fun p : ℝ × ℝ ↦
      ((1 - p.2) • (1 : CMatrix a) + p.2 • (σ + p.1 • X))⁻¹) rect p
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using
      (hi.comp (f := fun p : ℝ × ℝ ↦
        (1 - p.2) • (1 : CMatrix a) + p.2 • (σ + p.1 • X))
          (hc.continuousAt (x := p))).continuousWithinAt
  have hC : Continuous (fun p : ℝ × ℝ ↦ σ + p.1 • X - 1) := by fun_prop
  have hF : ContinuousOn F rect := hC.continuousOn.mul hR
  have hG : ContinuousOn G rect := (hR.mul continuousOn_const).mul hR
  have hd : ∀ u ∈ Set.Icc (-ε) ε, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ ↦ F (v, t)) (G (u, t)) u := by
    intro u hu t ht
    exact log_resolvent_integrand_hasDerivAt (logResolvent_posDef (hpos u hu) ht).isUnit
  have hh := hasDerivAt_integral_compact_rectangle hε F G hF hG hd
  have heq : (fun u : ℝ ↦ CFC.log (σ + u • X)) =ᶠ[𝓝 0]
      (fun u : ℝ ↦ ∫ t : ℝ in 0..1, F (u, t)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with u hu
    exact log_eq_integral_resolvent (hpos u ⟨hu.1.le, hu.2.le⟩)
  apply (hh.congr_of_eventuallyEq heq).congr_deriv
  simpa [G, R] using (inverseKuboMori_eq_integral_resolvent hσ X).symm

theorem log_hasDerivAt_affine [Nonempty a] {σ X : CMatrix a} {u : ℝ}
    (hσ : (σ + u • X).PosDef) (hX : X.IsHermitian) :
    HasDerivAt (fun v : ℝ ↦ CFC.log (σ + v • X)) (inverseKuboMori hσ X) u := by
  have hh := (log_hasDerivAt_affine_zero hσ hX).scomp_of_eq u
    ((hasDerivAt_id u).sub_const u) (by simp)
  have heq (v : ℝ) : σ + u • X + (v - u) • X = σ + v • X := by module
  simpa only [sub_self, Function.comp_def, heq, one_smul, id_eq] using hh

end QuanIncapacity.BKM
