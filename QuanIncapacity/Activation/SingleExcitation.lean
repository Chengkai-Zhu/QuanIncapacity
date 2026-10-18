import QuanIncapacity.Activation.QubitRestriction

/-!
# The single-excitation dephased-erasure channel

On the single-excitation subspace of `d` qubits (spanned by `|e_j⟩ = |0⟩^{⊗(j−1)}|1⟩|0⟩^{⊗(d−j)}`
together with the vacuum `|0⟩^{⊗d}`), the channel `C^{⊗d}` restricts to the
flagged dephased-erasure channel `T_{q,η}^{(d)} = q·𝒵_η ⊕ (1−q)Tr(ρ)|e⟩⟨e|`, with
`q = η = 1/4` and `𝒵_η = η·id + (1−η)·Δ`.

Here we record the two essential single-qubit coefficients and the concrete `d = 2`
tensorization `C ⊗ C` on the two-qubit space `(ℂ²)^{⊗2}`. The paper proves general
`d` by a tensor-factor argument; that general theorem is not formalized in this file.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators

namespace QuanIncapacity

open QuanIncapacity
open QIT

/- The two-qubit tensor product `C ⊗ C` of the qubit restriction. -/
def tensorC2 : MatrixMap (Prod (Fin 2) (Fin 2)) (Prod (Fin 2) (Fin 2)) :=
  MatrixMap.kron C_map C_map

/- Diagonal survival: `C(|1⟩⟨1|) = ¾|0⟩⟨0| + ¼|1⟩⟨1|`, so an excitation survives
  with probability `q = 1/4`. (Already given by `C_E11`.) -/
lemma excitation_survival_probability :
    C_map (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) (1 : Fin 2) (1 : Fin 2)
      = (1 / 4 : ℂ) := by
  rw [C_E11]
  simp [Matrix.smul_apply, Matrix.add_apply]

/- Off-diagonal coherence: `C(|0⟩⟨1|) = ¼|0⟩⟨1|`, so coherence between two
  locations survives with amplitude `c = 1/4` and `c² = 1/16`. (Given by `C_E01`.) -/
lemma coherence_survival_amplitude :
    C_map (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) (0 : Fin 2) (1 : Fin 2)
      = (1 / 4 : ℂ) := by
  rw [C_E01]
  simp [Matrix.smul_apply]

/- The dephasing factor `η = c²/q = 1/4`. -/
lemma eta_eq : ((1 / 4 : ℂ) ^ 2) / (1 / 4 : ℂ) = (1 / 4 : ℂ) := by norm_num

/- A matrix unit on a product index is a Kronecker product of matrix units:
  `|10⟩⟨10| = |1⟩⟨1| ⊗ |0⟩⟨0|`. -/
lemma single_prod_10_10 :
    Matrix.single ((1 : Fin 2), (0 : Fin 2)) ((1 : Fin 2), (0 : Fin 2)) (1 : ℂ) =
      Matrix.kronecker (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ))
        (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) :=
  single_prod_eq_kronecker_single (1 : Fin 2) (1 : Fin 2) (0 : Fin 2) (0 : Fin 2)

/- A matrix unit on a product index is a Kronecker product of matrix units:
  `|10⟩⟨01| = |1⟩⟨0| ⊗ |0⟩⟨1|`. -/
lemma single_prod_10_01 :
    Matrix.single ((1 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ) =
      Matrix.kronecker (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ))
        (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) :=
  single_prod_eq_kronecker_single (1 : Fin 2) (0 : Fin 2) (0 : Fin 2) (1 : Fin 2)

/- The diagonal single-excitation state `|10⟩⟨10|` is mapped by `C ⊗ C` to
  `¼|10⟩⟨10| + ¾|00⟩⟨00|`: the excitation survives with probability `¼` and decays
  to the vacuum with probability `¾`. -/
lemma tensorC2_diag_excitation :
    tensorC2 (Matrix.single ((1 : Fin 2), (0 : Fin 2)) ((1 : Fin 2), (0 : Fin 2)) (1 : ℂ)) =
      (1 / 4 : ℂ) • Matrix.single ((1 : Fin 2), (0 : Fin 2)) ((1 : Fin 2), (0 : Fin 2)) (1 : ℂ)
        + (3 / 4 : ℂ) • Matrix.single ((0 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ) := by
  rw [tensorC2]
  rw [single_prod_10_10]
  rw [MatrixMap.kron_apply_kronecker]
  rw [C_E11, C_E00]
  ext x y
  cases x with
  | mk x1 x2 =>
    cases y with
    | mk y1 y2 =>
      fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
        simp [Matrix.kronecker, Matrix.smul_apply, Matrix.add_apply] <;> norm_num

/- The off-diagonal single-excitation state `|10⟩⟨01|` is mapped by `C ⊗ C` to
  `(1/16)|10⟩⟨01|`: the two-location coherence survives with amplitude `c² = 1/16`. -/
lemma tensorC2_offdiag_excitation :
    tensorC2 (Matrix.single ((1 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ)) =
      (1 / 16 : ℂ) • Matrix.single ((1 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ) := by
  rw [tensorC2]
  rw [single_prod_10_01]
  rw [MatrixMap.kron_apply_kronecker]
  rw [C_E10, C_E01]
  ext x y
  cases x with
  | mk x1 x2 =>
    cases y with
    | mk y1 y2 =>
      fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
        simp [Matrix.kronecker, Matrix.smul_apply] <;> norm_num

end QuanIncapacity
