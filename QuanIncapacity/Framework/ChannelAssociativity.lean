import QuanIncapacity.Framework.ChannelTensorTransport

/-! Associating three channel factors uses an actual isometric encoder
and an inverse permutation channel, including arbitrary reference inputs. -/

noncomputable section
open QIT
open scoped Matrix

namespace QuanIncapacity

variable {a b c d e f : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
variable [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]

theorem simulation_prod_assoc (N : Channel a b) (M : Channel c d) (P : Channel e f) :
    Simulates ((N.prod M).prod P) (N.prod (M.prod P)) := by
  refine ⟨ReferenceIsometry.ofEquiv (Equiv.prodAssoc a c e),
    Channel.reindex (Equiv.prodAssoc b d f).symm, ?_⟩
  apply channel_eq_of_single
  intro i j
  change (Channel.reindex _).map ((N.prod (M.prod P)).map
    ((Channel.reindex (Equiv.prodAssoc a c e)).map (Matrix.single i j 1))) = _
  rw [channel_reindex_map (Equiv.prodAssoc a c e), Matrix.submatrix_single_equiv,
    channel_reindex_map,
    single_prod_eq_kronecker_single, Channel.prod_map_kronecker,
    single_prod_eq_kronecker_single, Channel.prod_map_kronecker,
    single_prod_eq_kronecker_single, Channel.prod_map_kronecker,
    single_prod_eq_kronecker_single, Channel.prod_map_kronecker]
  ext ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩
  simp only [Matrix.submatrix_apply, Equiv.symm_symm, Equiv.prodAssoc_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

end QuanIncapacity
