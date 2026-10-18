import QuanIncapacity
import Lean.Util.CollectAxioms

/-!
Independent terminal-type checks and a transitive axiom audit of all local
declarations, including private declarations. Operational theorem parameters
are displayed explicitly.
-/

noncomputable section
open scoped ComplexOrder MatrixOrder BigOperators Matrix
open QIT QuanIncapacity MeasureTheory

example : MatrixMap.IsCompletelyPositive Λ.map := Λ.completelyPositive
example : MatrixMap.IsTracePreserving Λc.map := Λc.tracePreserving
example (Y : CMatrix (Fin 3)) :
    MatrixMap.krausAdjoint Ec (𝒥_map Y) = Λ_map Y := 𝒥_lift Y
example : Δ_defect = Δ := Δ_defect_eq_Δ
example : MatrixMap.IsCompletelyPositive Δ := Δ_completelyPositive
example : IsScalarShadowMap Λ_map Λc_map 𝒥_map := qutrit_scalar_shadow_map
example : IsCompleteShadowMap Λ_map Λc_map 𝒥_map := qutrit_complete_shadow_map
example : Shadowing.IsCompleteShadow Λ_map Λc_map 𝒥_map := qutrit_complete_shadow
example : ComplementaryChannels Λ Λc := qutrit_complementary
example : CompleteRelativeEntropyOrder Λ Λc := qutrit_complete_relativeEntropy_order
example {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b] [Fintype e] [DecidableEq e] [Nonempty e]
    (N : Channel a b) (M : Channel a e) (hN : (N.map 1).PosDef) (hM : (M.map 1).PosDef)
    (h : CompleteBKMOrder N M hN hM) : CompleteRelativeEntropyOrder N M := h.relativeEntropyOrder
example : QutritAllBlockZeroInformation := qutrit_all_block_zero_information
example (n : ℕ) : Information.privateOneShot (Λ.tensorPower n) (Λc.tensorPower n) = 0 :=
  qutrit_privateOneShot_zero n
example (n : ℕ) : (Λ.tensorPower n).coherentInformation = 0 := qutrit_coherentInformation_zero n
example (coding : External.PrivateCoding Λ Λc) : PrivateCoding.capacity Λ Λc = 0 :=
  qutrit_privateCapacity_zero coding
example (coding : External.QuantumCoding Λ) : Λ.quantumCapacity = 0 :=
  qutrit_quantumCapacity_zero coding
example : coherentInfoMax = 0 := qutrit_coherentInfoMax_zero
example : privateInfoMax = 0 := qutrit_privateInfoMax_zero
example (r : Type) [Fintype r] [DecidableEq r]
    (τ X : CMatrix (r × Fin 3)) (hτ : τ.PosDef) :
    BKM.metric (MatrixSpace.amp_posDef Λ qutrit_identity_output_posDef hτ)
        (MatrixSpace.amp r Λ_map X) ≤
      BKM.metric (MatrixSpace.amp_posDef Λc qutrit_environment_identity_output_posDef hτ)
        (MatrixSpace.amp r Λc_map X) :=
  qutrit_complete_bkm_order r τ X hτ
example {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
    (N : Channel a b) (M : Channel a e) (J : MatrixMap b e)
    (hJ : Shadowing.IsUnbiasedShadow N.map M.map J) :
    Shadowing.IsCompleteShadow N.map M.map J ↔
      MatrixMap.IsCompletelyPositive (Shadowing.outerDefect N.map M.map J) :=
  Shadowing.completeShadow_iff_outerDefect_cp N M J hJ
example : omega = (1 / 3 : ℂ) • MatrixMap.choi Λ.map := omega_eq_normalized_choi
example : ¬ (partialTransposeA ((1 / 3 : ℂ) • MatrixMap.choi Λ.map)).PosSemidef :=
  qutrit_choi_npt
example : ¬ ∃ D : Channel (Fin 4) (Fin 3), D.map.comp Λc_map = Λ_map :=
  qutrit_not_antidegradable
example : C_map (Matrix.single (0 : Fin 2) 0 (1 : ℂ)) = Matrix.single 0 0 1 := C_E00
example : V.conjTranspose * V = (1 : CMatrix (Fin 2)) := V_isometry
example : MatrixMap.IsTracePreserving C_map := by
  rw [← restrictedQubitChannel_map]
  exact restrictedQubitChannel.tracePreserving
example (n : ℕ) : (Excitation.encodedChannel n).map =
    DephasedErasure.map (a := Fin n) (1 / 4) (1 / 4) := Excitation.encodedChannel_map n
example (n : ℕ) : MatrixMap.IsTracePreserving (Excitation.encodedChannel n).map :=
  (Excitation.encodedChannel n).tracePreserving
example (q η : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    MatrixMap.IsCompletelyPositive (DephasedErasure.map (a := Fin 1) q η) := by
  rw [← DephasedErasure.channel_map q η hq0 hq1 hη0 hη1]
  exact (DephasedErasure.channel q η hq0 hq1 hη0 hη1).completelyPositive
example (ρ σ : State (Fin 2 × Fin 3)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * ρ.coherentInformation + p * σ.coherentInformation - QIT.binaryEntropy p ≤
      (State.binaryMix p ρ σ hp0 hp1).coherentInformation :=
  Activation.coherentInformation_binaryMix_ge p ρ σ hp0 hp1
example : MatrixMap.IsTracePreserving M_H.map := M_H.tracePreserving
example : MatrixMap.choi M_H.map = (4 : ℝ) • regrouped OmegaH := M_H_choi
example : (partialTransposeB (MatrixMap.choi M_H.map)).PosSemidef := M_H_choi_ppt
example : 0 < 1 - binaryEntropy qH := helper_entropy_gap_pos

example (ρ : State (Fin 3)) (Y : CMatrix (Fin 3)) (hY : Y.IsHermitian) :
    Var (Λ.applyState ρ).matrix Y - Var (Λc.applyState ρ).matrix (𝒥_map Y) =
      (2 / 9 : ℝ) * ∑ μ : Fin 3, ∑ i : Fin 3,
        Complex.normSq ((ρ.sqrtMatrix *ᵥ residual μ Y) i) :=
  qutrit_variance_sum_normSq ρ Y hY
example (ρ : State (Fin 3)) (hρ : ρ.matrix.PosDef)
    (Y : CMatrix (Fin 3)) (hY : Y.IsHermitian) :
    Var (Λ.applyState ρ).matrix Y = Var (Λc.applyState ρ).matrix (𝒥_map Y) ↔
      Y = (Y.trace / 3) • (1 : CMatrix (Fin 3)) := qutrit_variance_eq_iff_scalar ρ hρ Y hY
example : (MatrixMap.choi Δ).rank = 3 := DefectSpectrum.choi_rank
example : Module.finrank ℂ (MatrixMap.choi Δ).mulVecLin.ker = 24 :=
  DefectSpectrum.choi_kernel_finrank
example : (MatrixMap.choi Δ).charpoly =
    Polynomial.X ^ 24 * (Polynomial.X - Polynomial.C (8 / 9 : ℂ)) ^ 3 :=
  DefectSpectrum.choi_charpoly
example : (ptA omega).charpoly =
    (Polynomial.X - Polynomial.C (1 / 4 : ℂ)) ^ 5 * Polynomial.X *
      (Polynomial.X + Polynomial.C (1 / 12 : ℂ)) ^ 3 := ChoiSpectrum.charpoly_eq
example : (ptA omega).rank = 8 := ChoiSpectrum.rank
example : SchmidtWitness.coefficient.rank = 2 := SchmidtWitness.coefficient_rank
example : star SchmidtWitness.vector.amp ⬝ᵥ (ptA omega *ᵥ SchmidtWitness.vector.amp) =
    (-1 / 12 : ℂ) := SchmidtWitness.expectation
example : MatrixMap.kron OneCopyFilter.map OneCopyFilter.map qutritChoiState.matrix =
    OneCopyFilter.branch := OneCopyFilter.actual_success_branch
example : OneCopyFilter.branch.trace = (1 / 2 : ℂ) := OneCopyFilter.branch_trace
example : ¬ IsSeparable OneCopyFilter.output := OneCopyFilter.output_entangled
example (criterion : External.SchmidtRankTwoDistillation) :
    0 < Distillation.capacity qutritChoiState := qutritChoi_twoWay_distillable criterion
example (forward : External.ForwardClassicalNoIncreaseQuantumCapacity Λ)
    (coding : External.QuantumCoding Λ) : Distillation.oneWayCapacity qutritChoiState = 0 :=
  qutritChoi_oneWay_zero forward coding
example {a : Type} [Fintype a] [DecidableEq a] :
    ComplementaryChannels (HalfErasure.channel (a := a)) HalfErasure.channel :=
  HalfErasure.complementary
example {e : Type} [Fintype e] [DecidableEq e]
    (N : Channel (Fin 4) (Fin 4)) (M : Channel (Fin 4) e)
    (hc : ComplementaryChannels N M)
    (imported : External.FourDimensionalPrivateSuperactivation N M)
    (pc : External.PrivateCoding NonprivateActivation.secondFactor
      NonprivateActivation.secondComplement)
    (qc : External.QuantumCoding (N.prod NonprivateActivation.secondFactor)) :
    PrivateCoding.capacity N M = 0 ∧
      PrivateCoding.capacity NonprivateActivation.secondFactor
        NonprivateActivation.secondComplement = 0 ∧
      0 < (N.prod NonprivateActivation.secondFactor).quantumCapacity :=
  NonprivateActivation.two_nonprivate N M hc imported pc qc
example (γ : ℝ) (h0 : 0 < γ) (hh : γ < 1 / 2)
    (qc : External.QuantumCoding (AmplitudeDamping.channel γ h0.le (by linarith))) :
    0 < (AmplitudeDamping.channel γ h0.le (by linarith)).quantumCapacity :=
  AmplitudeDamping.quantumCapacity_pos γ h0 hh qc

#print QuanIncapacity.External.SchmidtRankTwoDistillation
#print QuanIncapacity.External.ForwardClassicalNoIncreaseQuantumCapacity
#print QuanIncapacity.External.FourDimensionalPrivateSuperactivation
#check QuanIncapacity.qutritChoi_twoWay_distillable
#check QuanIncapacity.qutritChoi_oneWay_zero
#check QuanIncapacity.NonprivateActivation.two_nonprivate
#check QuanIncapacity.AmplitudeDamping.quantumCapacity_pos
#print axioms QuanIncapacity.OneCopyFilter.one_copy_entangled_branch
#print axioms QuanIncapacity.DefectSpectrum.choi_charpoly
#print axioms QuanIncapacity.ChoiSpectrum.charpoly_eq
#print axioms QuanIncapacity.qutrit_variance_eq_iff_scalar

example {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι] (E : QIT.Ensemble ι a) :
    (E.holevoInformation : EReal) =
      ∑ i, ((E.probs i : ℝ) : EReal) * (E.states i).relativeEntropy E.averageState :=
  holevoInformation_eq_sum_relativeEntropy E
example {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (E : QIT.Ensemble ι a) :
    Fintype.card (Activation.Auxiliary E) = ∑ i, (E.states i).matrix.rank :=
  Activation.auxiliary_card E
example {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (E : QIT.Ensemble ι a) :
    Activation.dropAuxiliary (Activation.globalPurification E).state = E.cqState :=
  Activation.globalPurification_dropAuxiliary E
example {a b e ι : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e] [Fintype ι] [DecidableEq ι]
    (N : Channel a b) (M : Channel a e) (hc : ComplementaryChannels N M)
    (E : QIT.Ensemble ι a) (q η : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    q * η * (QuanIncapacity.Ensemble.mapChannel M E).cqState.conditionalEntropy - q * QIT.binaryEntropy η -
        (1 - q) * (QuanIncapacity.Ensemble.mapChannel N E).cqState.conditionalEntropy ≤
      (N.prod (DephasedErasure.channel q η hq0 hq1 hη0 hη1)).coherentInformationFor
        (Activation.globalPurification E) :=
  Activation.private_to_coherent_bound hc E q η hq0 hq1 hη0 hη1
example {a b e : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype e] [DecidableEq e] (N : Channel a b) (M : Channel a e)
    (hc : ComplementaryChannels N M) (hP : 0 < PrivateCoding.capacity N M) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ, ∃ (_ : NeZero k), ∃ C : HSWClassicalCode N n (Fin k),
      0 < Activation.codeConversionValue C := Activation.exists_finite_positive_block hc hP

#print axioms QuanIncapacity.holevoInformation_eq_sum_relativeEntropy
#print axioms QuanIncapacity.Activation.auxiliary_card
#print axioms QuanIncapacity.Activation.globalPurification_dropAuxiliary
#print axioms QuanIncapacity.Activation.private_to_coherent_bound
#print axioms QuanIncapacity.Activation.code_holevo_fano
#print axioms QuanIncapacity.Activation.exists_finite_positive_block
#check @QuanIncapacity.Activation.private_to_coherent_bound
#check @QuanIncapacity.Activation.exists_finite_positive_block

example {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
    (N : Channel a b) (M : Channel a e) (hc : ComplementaryChannels N M)
    (hP : 0 < PrivateCoding.capacity N M)
    (coding : External.QuantumCoding (N.prod Λ)) : 0 < (N.prod Λ).quantumCapacity :=
  Activation.universal_activation hc hP coding

example : Var (Λ.applyState (State.maximallyMixed (Fin 3))).matrix
    (Matrix.single (0 : Fin 3) 0 1) = 2 / 9 := qutrit_example_receiver_variance
example : Var (Λc.applyState (State.maximallyMixed (Fin 3))).matrix
    (𝒥_map (Matrix.single (0 : Fin 3) 0 1)) = 1 / 9 := qutrit_example_environment_variance

#print axioms QuanIncapacity.Activation.universal_activation
#print axioms QuanIncapacity.Activation.exists_positive_product_block
#check @QuanIncapacity.Activation.universal_activation
#check @QuanIncapacity.Activation.positive_padded_code
#print axioms QuanIncapacity.G_trace_orthogonal
#print axioms QuanIncapacity.qutrit_example_environment_variance

example {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
    (N : Channel a b) (M : Channel a e) (J : MatrixMap b e)
    (h : Shadowing.IsCompleteShadow N.map M.map J) : CompleteRelativeEntropyOrder N M :=
  Shadowing.complete_relativeEntropy_order_of_shadow N M J h
example : ComplementaryChannels M_H Helper.complement := Helper.complementary
example : Information.privateInfo M_H Helper.complement Helper.ensemble =
    1 - QIT.binaryEntropy qH := Helper.privateInfo_eq
example : 1 - QIT.binaryEntropy qH ≤ Information.privateOneShot M_H Helper.complement :=
  Helper.privateOneShot_lower
example : M_H.quantumCapacity = 0 := Helper.quantumCapacity_zero
example (codingP : External.PrivateCoding M_H Helper.complement)
    (codingQ : External.QuantumCoding (M_H.prod Λ)) : 0 < (M_H.prod Λ).quantumCapacity :=
  Helper.activation codingP codingQ

#print axioms QuanIncapacity.Shadowing.complete_relativeEntropy_order_of_shadow
#check @QuanIncapacity.Shadowing.privateCapacity_eq_zero
#check @QuanIncapacity.Shadowing.quantumCapacity_eq_zero
#print axioms QuanIncapacity.Helper.complementary
#print axioms QuanIncapacity.Helper.privateInfo_eq
#print axioms QuanIncapacity.PPT.quantumCapacity_eq_zero
#print axioms QuanIncapacity.Helper.superactivation
#check @QuanIncapacity.Helper.activation
#check @QuanIncapacity.Helper.superactivation

#print axioms QuanIncapacity.𝒥_lift
#print axioms QuanIncapacity.Δ_defect_eq_Δ
#print axioms QuanIncapacity.qutrit_scalar_shadow_map
#print axioms QuanIncapacity.qutrit_complete_shadow_map
#print axioms QuanIncapacity.Shadowing.completeShadow_iff_outerDefect_cp
#print axioms QuanIncapacity.qutrit_complementary
#print axioms QuanIncapacity.MatrixSpace.inverse_variational_sup
#print axioms QuanIncapacity.MatrixSpace.inverse_variational_eq_iff
#print axioms QuanIncapacity.MatrixSpace.arithmetic_inverse_comparison
#print axioms QuanIncapacity.MatrixSpace.arithmeticMetric_comparison
#print axioms QuanIncapacity.shadow_adjoint_eq_hsAdjoint
#print axioms QuanIncapacity.BKM.integral_arithmetic_inverse
#print axioms QuanIncapacity.BKM.integral_geometric
#print axioms QuanIncapacity.MatrixSpace.arithmeticMetric_diagonal
#print axioms QuanIncapacity.qutrit_complete_arithmeticMetric_order
#print axioms QuanIncapacity.BKM.kuboMori_eq_integral
#print axioms QuanIncapacity.BKM.inverseKuboMori_kuboMori
#print axioms QuanIncapacity.BKM.kuboMori_inverseKuboMori
#print axioms QuanIncapacity.BKM.left_weight_to_bkm
#print axioms QuanIncapacity.qutrit_complete_bkm_order
#print axioms QuanIncapacity.BKM.log_hasDerivAt_affine
#print axioms QuanIncapacity.BKM.relativeEntropy_eq_integral_of_posDef
#print axioms QuanIncapacity.BKM.relativeEntropy_common_regularization_tendsto
#print axioms QuanIncapacity.qutrit_complete_relativeEntropy_order
#print axioms QuanIncapacity.CompleteBKMOrder.relativeEntropyOrder
#print axioms QuanIncapacity.CompleteRelativeEntropyOrder.prod
#print axioms QuanIncapacity.ComplementaryChannels.prod
#print axioms QuanIncapacity.ComplementaryChannels.mutualInformation_sub_eq
#print axioms QuanIncapacity.qutrit_all_block_zero_information
#print axioms QuanIncapacity.qutrit_privateOneShot_zero
#print axioms QuanIncapacity.qutrit_coherentInformation_zero
#print axioms QuanIncapacity.qutrit_privateCapacity_zero
#print axioms QuanIncapacity.qutrit_quantumCapacity_zero
#check QuanIncapacity.qutrit_privateCapacity_zero
#check QuanIncapacity.qutrit_quantumCapacity_zero
#print QuanIncapacity.External.QuantumCoding
#print QuanIncapacity.External.PrivateCoding
#print axioms QuanIncapacity.qutrit_not_antidegradable
#print axioms QuanIncapacity.qutrit_choi_npt
#print axioms QuanIncapacity.C_E00
#print axioms QuanIncapacity.tensorC2_offdiag_excitation
#print axioms QuanIncapacity.Excitation.encodedChannel_map
#print axioms QuanIncapacity.Excitation.physicalChannel_supported
#print axioms QuanIncapacity.DephasedErasure.channel_map
#print axioms QuanIncapacity.Activation.coherentInformation_binaryMix_ge
#print axioms QuanIncapacity.Activation.receiverFlaggedState_coherentInformation
#print axioms QuanIncapacity.qutrit_partner_private_zero
#print axioms QuanIncapacity.qutrit_partner_quantum_zero
#check QuanIncapacity.qutrit_partner_private_zero
#check QuanIncapacity.qutrit_partner_quantum_zero
#print axioms QuanIncapacity.M_H_choi_ppt

open scoped Matrix.Norms.Elementwise Topology

example {a : Type} [Fintype a] [DecidableEq a] (σ X : CMatrix a)
    (hσ : σ.PosDef) (hX : X.IsHermitian) :
    BKM.metric hσ X = ∫ t : ℝ in Set.Ici 0,
      (X * (σ + t • (1 : CMatrix a))⁻¹ * X * (σ + t • (1 : CMatrix a))⁻¹).trace.re :=
  BKM.metric_eq_integral_Ici hσ X hX
example {a b e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
    (N : Channel a b) (M : Channel a e) (m n : ℕ) :
    Information.privateOneShot (N.tensorPower m) (M.tensorPower m) +
      Information.privateOneShot (N.tensorPower n) (M.tensorPower n) ≤
        Information.privateOneShot (N.tensorPower (m + n)) (M.tensorPower (m + n)) :=
  Information.private_superadditive N M m n
example {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] (N : Channel a b) :
    Filter.Tendsto (fun n : ℕ ↦ (N.tensorPower n).coherentInformation / n)
      Filter.atTop (𝓝 N.regularizedCoherentInformation) := coherent_rate_tendsto N
example {a b e : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]
    (M : Channel a e) (D : Channel e b) :
    Shadowing.IsCompleteShadow (D.comp M).map M.map (MatrixSpace.hsAdjoint D.map) :=
  Shadowing.complete_shadow_of_physical M D
example : Helper.support * Helper.keyZ * Helper.support = 0 := Helper.support_orthogonality
example : Helper.density.rank = 6 := Helper.density_rank
example : Module.finrank ℂ (LinearMap.range (SectorDimensions.projection 1)) = 5 :=
  by simpa using SectorDimensions.dimensions 1
#check ObservableStatistics.born_mean
#check ObservableStatistics.born_variance
#check ObservableStatistics.observable_sample_mean_expectation
#check Shadowing.complete_shadow_sample_mean
#check Shadowing.shadow_sample_mean_unbiased
#check ComplementaryChannels.coherent_maximum
#check Information.private_rate_tendsto
#check privateCapacity_rate_tendsto
#check quantumCapacity_rate_tendsto
#check NonprivateActivation.exists_two_nonprivate
#print External.FourDimensionalPrivateSuperactivationWitness

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? name with
      | some idx => (`QuanIncapacity).isPrefixOf (env.header.moduleNames[idx.toNat]!)
      | none => false
    if localModule then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved transitive axiom {ax} in {name}"
      checked := checked + 1
  if checked = 0 then
    throwError "No local declarations were audited"
  Lean.logInfo m!"Axiom audit passed: {checked} declarations from local modules; only propext, Classical.choice, Quot.sound permitted."
