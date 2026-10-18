import QuanIncapacity.Activation.GlobalPurification
import QuanIncapacity.Activation.RecordedReference

/-! The constructed conditional purification and its actual channel outputs.
The auxiliary trace and the dephased branch are identified by matrix equality. -/

noncomputable section
open QIT
open scoped BigOperators

namespace QuanIncapacity.Activation

variable {r a b c ι : Type} [Fintype r] [DecidableEq r]
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype ι] [DecidableEq ι]

def middleOutput (N : Channel a b) (ρ : State (r × (a × c))) : State (r × (b × c)) :=
  ((Channel.idChannel r).prod (N.prod (Channel.idChannel c))).applyState ρ

theorem middleOutput_matrix (N : Channel a b) (ρ : State (r × (a × c)))
    (x y : r) (u v : b) (i j : c) :
    (middleOutput N ρ).matrix (x, (u, i)) (y, (v, j)) =
      N.map (fun k l ↦ ρ.matrix (x, (k, i)) (y, (l, j))) u v := by
  calc
    _ = (N.prod (Channel.idChannel c)).map
        (fun k l ↦ ρ.matrix (x, k) (y, l)) (u, i) (v, j) :=
      MatrixMap.kron_idChannel_left_apply_slice _ ρ.matrix (x, (u, i)) (y, (v, j))
    _ = _ := MatrixMap.kron_idChannel_apply_slice N.map
      (fun k l ↦ ρ.matrix (x, k) (y, l)) (u, i) (v, j)

theorem dropAuxiliary_middleOutput (N : Channel a b) (ρ : State (r × (a × c))) :
    dropAuxiliary (middleOutput N ρ) =
      ((Channel.idChannel r).prod N).applyState (dropAuxiliary ρ) := by
  apply State.ext
  ext ⟨x, u⟩ ⟨y, v⟩
  let F : c → CMatrix a := fun k ↦ Matrix.of (fun i j ↦ ρ.matrix (x, (i, k)) (y, (j, k)))
  have heq : Matrix.of (fun i j ↦ (dropAuxiliary ρ).matrix (x, i) (y, j)) = ∑ k, F k := by
    ext i j
    simp [F, dropAuxiliary_matrix, Matrix.sum_apply]
  calc
    _ = ∑ k, N.map (F k) u v := by
      rw [dropAuxiliary_matrix]
      simp only [middleOutput_matrix]
      rfl
    _ = (∑ k, N.map (F k)) u v := (Matrix.sum_apply _ _ _ _).symm
    _ = N.map (∑ k, F k) u v :=
      (congrFun (congrFun (map_sum N.map F Finset.univ) u) v).symm
    _ = _ := by
      rw [← heq]
      exact (MatrixMap.kron_idChannel_left_apply_slice N.map (dropAuxiliary ρ).matrix
        (x, u) (y, v)).symm

def signalOutput (N : Channel a b) (E : Ensemble ι a) : State (ι × (b × Auxiliary E)) :=
  middleOutput N (globalPurification E).state

theorem signalOutput_dropAuxiliary (N : Channel a b) (E : Ensemble ι a) :
    dropAuxiliary (signalOutput N E) = (Ensemble.mapChannel N E).cqState := by
  rw [signalOutput, dropAuxiliary_middleOutput, globalPurification_dropAuxiliary,
    applyState_id_prod_cqState]

theorem signalOutput_supported (N : Channel a b) (E : Ensemble ι a)
    (x y : ι) (u v : b) (i j : Auxiliary E) (h : x ≠ i.1 ∨ y ≠ j.1) :
    (signalOutput N E).matrix (x, (u, i)) (y, (v, j)) = 0 := by
  rw [signalOutput, middleOutput_matrix]
  have hz : (fun k l ↦ (globalPurification E).state.matrix (x, (k, i)) (y, (l, j))) =
      (0 : CMatrix a) := by
    ext k l
    simp only [PureVector.state_matrix_apply]
    rcases h with hx | hy
    · rw [globalPurification_supported E x k i hx, zero_mul]
      rfl
    · rw [globalPurification_supported E y l j hy, star_zero, mul_zero]
      rfl
  rw [hz, map_zero]
  rfl

theorem signalOutput_dephased_coherentInformation (N : Channel a b) (E : Ensemble ι a) :
    (DephasedErasure.dephasedBranch (signalOutput N E)).coherentInformation = 0 :=
  DephasedErasure.dephasedBranch_coherentInformation_zero (signalOutput N E) Sigma.fst
    (signalOutput_supported N E)

end QuanIncapacity.Activation
