import QuanIncapacity.Qutrit.Defect

/-!
# The exact qubit restriction `C = R ∘ Λ ∘ V`

Encode a qubit into the span of `|g⟩ = (|0⟩+i|1⟩)/√2` and `|2⟩`, apply `Λ`, and
decode with Kraus operators `R₀ = |0⟩⟨2| − |1⟩⟨k|`, `R₁ = |0⟩⟨g|`. The resulting
qubit channel satisfies
`C(E₀₀)=E₀₀`, `C(E₁₁)=¾E₀₀+¼E₁₁`, `C(E₀₁)=¼E₀₁`, `C(E₁₀)=¼E₁₀`.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder BigOperators
open QIT

namespace QuanIncapacity

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open QuanIncapacity

private lemma qubit_sqrt_four : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
  calc
    _ = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
    _ = 4 := by rw [sqrt_two_sq]; norm_num

/- The vectors `|g⟩` and `|k⟩ = |g⟩*` in `ℂ³`. -/
def gvec : Fin 3 → ℂ := fun i => if i = 0 then (1 / Real.sqrt 2 : ℂ) else if i = 1 then (Complex.I / Real.sqrt 2) else 0

def kvec : Fin 3 → ℂ := fun i => if i = 0 then (1 / Real.sqrt 2 : ℂ) else if i = 1 then (-Complex.I / Real.sqrt 2) else 0

/- The encoder `V : ℂ² → ℂ³`, `V|0⟩=|g⟩`, `V|1⟩=|2⟩`. -/
def V : Matrix (Fin 3) (Fin 2) ℂ := Matrix.of fun i j => if j = 0 then gvec i else (if i = 2 then 1 else 0)

/- The decoder Kraus operators `R₀ = |0⟩⟨2| − |1⟩⟨k|`, `R₁ = |0⟩⟨g|`. -/
def R0 : Matrix (Fin 2) (Fin 3) ℂ :=
  Matrix.of fun i j ↦ if i = 0 then (if j = 2 then 1 else 0) else -star (kvec j)

def R1 : Matrix (Fin 2) (Fin 3) ℂ := Matrix.of fun i j ↦ if i = 0 then star (gvec j) else 0

/- The decoder is trace-preserving: `R₀†R₀ + R₁†R₁ = 𝟙₃`. -/
lemma R_tracePreserving : (R0.conjTranspose * R0 + R1.conjTranspose * R1) =
    (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R0, R1, gvec, kvec, sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply, Matrix.conjTranspose] <;>
    norm_num [map_ofNat] <;> ring_nf <;> simp [qubit_sqrt_four] <;> norm_num

lemma V_isometry : V.conjTranspose * V = (1 : CMatrix (Fin 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V, gvec, sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply, Matrix.conjTranspose_apply] <;>
    norm_num [map_ofNat] <;> ring_nf <;> simp [qubit_sqrt_four] <;> norm_num

def qubitEncoder : Channel (Fin 2) (Fin 3) where
  map := MatrixMap.ofKraus (fun _ : Unit ↦ V)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using V_isometry)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

def qubitDecoder : Channel (Fin 3) (Fin 2) where
  map := MatrixMap.ofKraus (fun i : Fin 2 ↦ if i = 0 then R0 else R1)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using R_tracePreserving)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/- The restricted channel `C = R ∘ Λ ∘ V`. -/
def C_map : MatrixMap (Fin 2) (Fin 2) :=
  MatrixMap.ofKraus (fun i : Fin 2 => if i = 0 then R0 else R1) |>.comp Λ_map |>.comp
    (MatrixMap.ofKraus (fun _ : Unit => V))

def restrictedQubitChannel : Channel (Fin 2) (Fin 2) :=
  (qubitDecoder.comp Λ).comp qubitEncoder

lemma restrictedQubitChannel_map : restrictedQubitChannel.map = C_map := rfl

/- The four matrix-unit actions of `C`. -/
lemma C_E00 : C_map (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) =
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_map, MatrixMap.ofKraus, Λ_map, V, R0, R1, gvec, kvec, sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply,
      Matrix.conjTranspose, Matrix.sum_apply, Matrix.trace, Matrix.transpose,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, sum_univ_three,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.I_mul_I] <;>
    norm_num [map_ofNat] <;> ring_nf <;> simp [qubit_sqrt_four] <;> ring

lemma C_E11 : C_map (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)) =
    (3 / 4 : ℂ) • Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
      + (1 / 4 : ℂ) • Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_map, MatrixMap.ofKraus, Λ_map, V, R0, R1, gvec, kvec, sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply,
      Matrix.conjTranspose, Matrix.sum_apply, Matrix.trace, Matrix.transpose,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, sum_univ_three,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.I_mul_I] <;>
    norm_num [map_ofNat] <;> ring_nf <;> simp [qubit_sqrt_four] <;> ring

lemma C_E01 : C_map (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)) =
    (1 / 4 : ℂ) • Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_map, MatrixMap.ofKraus, Λ_map, V, R0, R1, gvec, kvec, sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply,
      Matrix.conjTranspose, Matrix.sum_apply, Matrix.trace, Matrix.transpose,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, sum_univ_three,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.I_mul_I] <;>
    norm_num [map_ofNat] <;> ring_nf <;> simp [qubit_sqrt_four] <;> ring

lemma C_E10 : C_map (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)) =
    (1 / 4 : ℂ) • Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C_map, MatrixMap.ofKraus, Λ_map, V, R0, R1, gvec, kvec, sqrt_two_inv_eq_half_sqrt, Matrix.mul_apply,
      Matrix.conjTranspose, Matrix.sum_apply, Matrix.trace, Matrix.transpose,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, sum_univ_three,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.I_mul_I] <;>
    norm_num [map_ofNat] <;> ring_nf <;> simp [qubit_sqrt_four] <;> ring

end QuanIncapacity
