import QuanIncapacity.Qutrit.Lambda

/-!
# No antidegrading channel

Three computational-basis inputs impose reconstruction constraints incompatible
with positivity and trace preservation of an antidegrading channel.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators
open QIT
namespace QuanIncapacity

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

private def P (i : Fin 3) : CMatrix (Fin 3) := Matrix.single i i 1
private def Q (i : Fin 4) : CMatrix (Fin 4) := Matrix.single i i 1

private lemma basis_receiver (i : Fin 3) :
    (4 : ℂ) • Λ_map (P i) = 1 + P i := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [Λ_map, P, Matrix.trace, Matrix.smul_apply, Matrix.add_apply]

private lemma basis_environment (i : Fin 3) :
    (4 : ℂ) • Λc_map (P i) =
      (2 : ℂ) • Q 0 + Q 1 + Q 2 + Q 3 - Q i.succ := by
  ext a b
  change (4 : ℂ) * (K a * P i * (K b).conjTranspose).trace = _
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [P, Q, K, A, levN, fin4ToFin3, Matrix.mul_apply,
      Matrix.trace, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply]
  all_goals norm_num

/-- There is no CPTP reconstruction of the receiver from the full Kraus complement. -/
theorem qutrit_not_antidegradable :
    ¬ ∃ D : Channel (Fin 4) (Fin 3), D.map.comp Λc_map = Λ_map := by
  rintro ⟨D, hD⟩
  have hrec (i : Fin 3) : D.map (Λc_map (P i)) = Λ_map (P i) :=
    congrArg (fun f : MatrixMap (Fin 3) (Fin 3) ↦ f (P i)) hD
  have hc (i : Fin 3) :
      (2 : ℂ) • D.map (Q 0) + D.map (Q 1) + D.map (Q 2) + D.map (Q 3) -
        D.map (Q i.succ) = 1 + P i := by
    calc
      _ = D.map ((2 : ℂ) • Q 0 + Q 1 + Q 2 + Q 3 - Q i.succ) := by
        simp only [map_add, map_sub, map_smul]
      _ = D.map ((4 : ℂ) • Λc_map (P i)) := by rw [basis_environment]
      _ = (4 : ℂ) • Λ_map (P i) := by rw [map_smul, hrec]
      _ = 1 + P i := basis_receiver i
  have hpos (a : Fin 4) (i : Fin 3) : 0 ≤ (D.map (Q a) i i).re :=
    (Complex.nonneg_iff.mp
      ((D.mapsPositive (Q a) (QIT.posSemidef_single a)).diag_nonneg (i := i))).1
  have hdiag (i : Fin 3) : (D.map (Q 0) i i).re = 0 := by
    have h0 := congrArg (fun M : CMatrix (Fin 3) ↦ (M i i).re) (hc 0)
    have h1 := congrArg (fun M : CMatrix (Fin 3) ↦ (M i i).re) (hc 1)
    have h2 := congrArg (fun M : CMatrix (Fin 3) ↦ (M i i).re) (hc 2)
    have hs := hpos 0 i
    have ht := hpos i.succ i
    fin_cases i <;>
      norm_num [P, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Complex.mul_re] at h0 h1 h2 hs ht ⊢ <;> linarith
  have htrace : (D.map (Q 0)).trace = 1 := by
    rw [D.tracePreserving]
    simp [Q, Matrix.trace]
  have hre := congrArg Complex.re htrace
  simp only [Matrix.trace, Matrix.diag_apply, sum_univ_three, Complex.add_re,
    hdiag, Complex.one_re, add_zero] at hre
  norm_num at hre

end QuanIncapacity
