import QuanIncapacity.Framework.CompleteRelativeEntropy
import QIT.Util.TensorPower
import QIT.Information.Entropy.RelativeEntropyDPI
import QuanIncapacity.Framework.ChannelPair

/-! Tensor stability of the complete relative-entropy order, with explicit
reference permutations and channel composition. -/

noncomputable section
open QIT
open scoped ComplexOrder MatrixOrder

namespace QuanIncapacity

variable {a b c d e f g : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
variable [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
variable [Fintype g] [DecidableEq g]

theorem state_reindex_symm (ρ : State a) (v : a ≃ b) :
    (ρ.reindex v).reindex v.symm = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex_matrix, Matrix.submatrix]

theorem relativeEntropy_reindex (ρ σ : State a) (v : a ≃ b) :
    (ρ.reindex v).relativeEntropy (σ.reindex v) = ρ.relativeEntropy σ := by
  apply le_antisymm
  · simpa only [Channel.reindex_applyState] using
      State.relativeEntropy_dataProcessing_channel_ge ρ σ (Channel.reindex v)
  · simpa only [Channel.reindex_applyState, state_reindex_symm] using
      State.relativeEntropy_dataProcessing_channel_ge (ρ.reindex v) (σ.reindex v)
        (Channel.reindex v.symm)

theorem supports_reindex {ρ σ : State a} (h : Matrix.Supports ρ.matrix σ.matrix)
    (v : a ≃ b) : Matrix.Supports (ρ.reindex v).matrix (σ.reindex v).matrix := by
  have hh := State.channel_map_supports (Channel.reindex v) σ.pos h
  change Matrix.Supports ((Channel.reindex v).applyState ρ).matrix
    ((Channel.reindex v).applyState σ).matrix at hh
  simpa only [Channel.reindex_applyState] using hh

theorem prod_applyState_comp (N : Channel a b) (M : Channel c d)
    (P : Channel e a) (Q : Channel f c) (ρ : State (e × f)) :
    (N.prod M).applyState ((P.prod Q).applyState ρ) =
      ((N.comp P).prod (M.comp Q)).applyState ρ := by
  apply State.ext
  exact MatrixMap.kron_comp_apply_general N.map M.map P.map Q.map ρ.matrix

theorem idChannel_map_eq (a : Type) [Fintype a] [DecidableEq a] :
    (Channel.idChannel a).map = LinearMap.id := by
  ext X i j
  simp [Channel.idChannel, MatrixMap.ofKraus]

theorem amp_applyState_comp (N : Channel a b) (P : Channel c a)
    {r : Type} [Fintype r] [DecidableEq r] (ρ : State (r × c)) :
    ((Channel.idChannel r).prod N).applyState
        (((Channel.idChannel r).prod P).applyState ρ) =
      ((Channel.idChannel r).prod (N.comp P)).applyState ρ := by
  apply State.ext
  change MatrixMap.kron _ _ (MatrixMap.kron _ _ _) =
    MatrixMap.kron (Channel.idChannel r).map (N.map.comp P.map) ρ.matrix
  rw [MatrixMap.kron_comp_apply_general]
  simp only [idChannel_map_eq, LinearMap.id_comp]

/-- Move the last factor into the reference register. -/
def referenceLast (r a c : Type) : r × (a × c) ≃ (r × c) × a where
  toFun x := ((x.1, x.2.2), x.2.1)
  invFun x := (x.1.1, (x.2, x.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem applyState_prod_id_reindex (N : Channel a b)
    {r : Type} [Fintype r] [DecidableEq r] (ρ : State (r × (a × c))) :
    ((Channel.idChannel (r × c)).prod N).applyState
        (ρ.reindex (referenceLast r a c)) =
      (((Channel.idChannel r).prod (N.prod (Channel.idChannel c))).applyState ρ).reindex
        (referenceLast r b c) := by
  apply State.ext
  ext i j
  change MatrixMap.kron _ _ _ i j = _
  simp only [MatrixMap.kron_idChannel_left_apply_slice, State.reindex_matrix,
    Matrix.submatrix_apply]
  change N.map (fun k l ↦ ρ.matrix (i.1.1, (k, i.1.2)) (j.1.1, (l, j.1.2))) i.2 j.2 =
    MatrixMap.kron _ _ _ _ _
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  change N.map (fun k l ↦ ρ.matrix (i.1.1, (k, i.1.2)) (j.1.1, (l, j.1.2))) i.2 j.2 =
    MatrixMap.kron N.map (Channel.idChannel c).map _ _ _
  exact (MatrixMap.kron_idChannel_apply_slice N.map
    (fun x y ↦ ρ.matrix (i.1.1, x) (j.1.1, y)) (i.2, i.1.2) (j.2, j.1.2)).symm

theorem applyState_id_prod_reindex (N : Channel a b)
    {r : Type} [Fintype r] [DecidableEq r] (ρ : State (r × (c × a))) :
    ((Channel.idChannel (r × c)).prod N).applyState
        (ρ.reindex (Equiv.prodAssoc r c a).symm) =
      (((Channel.idChannel r).prod ((Channel.idChannel c).prod N)).applyState ρ).reindex
        (Equiv.prodAssoc r c b).symm := by
  apply State.ext
  ext i j
  change MatrixMap.kron _ _ _ i j = _
  simp only [MatrixMap.kron_idChannel_left_apply_slice, State.reindex_matrix,
    Matrix.submatrix_apply]
  change N.map (fun k l ↦ ρ.matrix (i.1.1, (i.1.2, k)) (j.1.1, (j.1.2, l))) i.2 j.2 =
    MatrixMap.kron _ _ _ _ _
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  change N.map (fun k l ↦ ρ.matrix (i.1.1, (i.1.2, k)) (j.1.1, (j.1.2, l))) i.2 j.2 =
    MatrixMap.kron (Channel.idChannel c).map N.map _ _ _
  exact (MatrixMap.kron_idChannel_left_apply_slice N.map
    (fun x y ↦ ρ.matrix (i.1.1, x) (j.1.1, y)) (i.1.2, i.2) (j.1.2, j.2)).symm

theorem prod_factor_right (N : Channel a b) (P : Channel c d) :
    (N.prod (Channel.idChannel d)).comp ((Channel.idChannel a).prod P) = N.prod P := by
  apply channel_eq_of_map_eq
  ext X i j
  change MatrixMap.kron _ _ (MatrixMap.kron _ _ _) i j = _
  rw [MatrixMap.kron_comp_apply_general]
  simp only [idChannel_map_eq, LinearMap.id_comp, LinearMap.comp_id]
  rfl

theorem prod_factor_left (P : Channel c d) (N : Channel a b) :
    ((Channel.idChannel d).prod N).comp (P.prod (Channel.idChannel a)) = P.prod N := by
  apply channel_eq_of_map_eq
  ext X i j
  change MatrixMap.kron _ _ (MatrixMap.kron _ _ _) i j = _
  rw [MatrixMap.kron_comp_apply_general]
  simp only [idChannel_map_eq, LinearMap.id_comp, LinearMap.comp_id]
  rfl

namespace CompleteRelativeEntropyOrder

theorem refl (N : Channel a b) : CompleteRelativeEntropyOrder N N :=
  fun _ _ _ _ _ _ _ ↦ le_rfl

theorem trans {N : Channel a b} {M : Channel a e} {P : Channel a f}
    (h : CompleteRelativeEntropyOrder N M) (h' : CompleteRelativeEntropyOrder M P) :
    CompleteRelativeEntropyOrder N P := fun r _ _ _ ρ σ hs ↦ (h r ρ σ hs).trans (h' r ρ σ hs)

theorem comp {N : Channel a b} {M : Channel a e}
    (h : CompleteRelativeEntropyOrder N M) (P : Channel c a) :
    CompleteRelativeEntropyOrder (N.comp P) (M.comp P) := by
  intro r _ _ _ ρ σ hs
  have hh := h r (((Channel.idChannel r).prod P).applyState ρ)
    (((Channel.idChannel r).prod P).applyState σ)
    (State.channel_map_supports _ σ.pos hs)
  simpa only [amp_applyState_comp] using hh

theorem prod_id [Nonempty c] {N : Channel a b} {M : Channel a e}
    (h : CompleteRelativeEntropyOrder N M) :
    CompleteRelativeEntropyOrder (N.prod (Channel.idChannel c))
      (M.prod (Channel.idChannel c)) := by
  intro r _ _ _ ρ σ hs
  have hh := h (r × c) (ρ.reindex (referenceLast r a c))
    (σ.reindex (referenceLast r a c)) (supports_reindex hs _)
  simpa only [applyState_prod_id_reindex, relativeEntropy_reindex] using hh

theorem id_prod [Nonempty c] {N : Channel a b} {M : Channel a e}
    (h : CompleteRelativeEntropyOrder N M) :
    CompleteRelativeEntropyOrder ((Channel.idChannel c).prod N)
      ((Channel.idChannel c).prod M) := by
  intro r _ _ _ ρ σ hs
  have hh := h (r × c) (ρ.reindex (Equiv.prodAssoc r c a).symm)
    (σ.reindex (Equiv.prodAssoc r c a).symm) (supports_reindex hs _)
  simpa only [applyState_id_prod_reindex, relativeEntropy_reindex] using hh

theorem prod_right [Nonempty d] {N : Channel a b} {M : Channel a e}
    (h : CompleteRelativeEntropyOrder N M) (P : Channel c d) :
    CompleteRelativeEntropyOrder (N.prod P) (M.prod P) := by
  simpa only [prod_factor_right] using
    (h.prod_id (c := d)).comp ((Channel.idChannel a).prod P)

theorem prod_left [Nonempty d] {N : Channel a b} {M : Channel a e}
    (h : CompleteRelativeEntropyOrder N M) (P : Channel c d) :
    CompleteRelativeEntropyOrder (P.prod N) (P.prod M) := by
  simpa only [prod_factor_left] using
    (h.id_prod (c := d)).comp (P.prod (Channel.idChannel a))

theorem prod [Nonempty d] [Nonempty e]
    {N : Channel a b} {M : Channel a e} {P : Channel c d} {Q : Channel c f}
    (h : CompleteRelativeEntropyOrder N M) (h' : CompleteRelativeEntropyOrder P Q) :
    CompleteRelativeEntropyOrder (N.prod P) (M.prod Q) :=
  (h.prod_right P).trans (h'.prod_left M)

theorem tensorPower [Nonempty b] [Nonempty e]
    {N : Channel a b} {M : Channel a e} (h : CompleteRelativeEntropyOrder N M) :
    ∀ n : ℕ, CompleteRelativeEntropyOrder (N.tensorPower n) (M.tensorPower n)
  | 0 => refl Channel.unit
  | n + 1 => by
      haveI : Nonempty (QIT.TensorPower b n) := tensorPower_nonempty_of_nonempty n
      exact h.prod (h.tensorPower n)

end CompleteRelativeEntropyOrder
end QuanIncapacity
