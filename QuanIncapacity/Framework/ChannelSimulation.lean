import QuanIncapacity.Framework.CoherentProcessing
import QuanIncapacity.Framework.ComplementaryTensor

/-! Exact channel simulation by an isometric encoder and a CPTP decoder.
These are physical constructions, and preserve arbitrary entanglement with
a reference. -/

noncomputable section
open QIT
open scoped Matrix

namespace QuanIncapacity

variable {a b c d e f g h : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
variable [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
variable [Fintype g] [DecidableEq g] [Fintype h] [DecidableEq h]

theorem channel_comp_assoc (N : Channel a b) (M : Channel b c) (P : Channel c d) :
    (P.comp M).comp N = P.comp (M.comp N) := channel_eq_of_map_eq _ _ rfl

theorem channel_prod_comp (N : Channel a b) (M : Channel c d)
    (P : Channel e a) (Q : Channel f c) :
    (N.prod M).comp (P.prod Q) = (N.comp P).prod (M.comp Q) := by
  apply channel_eq_of_map_eq
  ext X i j
  exact congrFun (congrFun (MatrixMap.kron_comp_apply_general N.map M.map P.map Q.map X) i) j

theorem isometryChannel_comp (V : ReferenceIsometry a b) (W : ReferenceIsometry b c) :
    Channel.ofReferenceIsometry (W.comp V) =
      (Channel.ofReferenceIsometry W).comp (Channel.ofReferenceIsometry V) := by
  apply channel_eq_of_map_eq
  apply LinearMap.ext
  intro X
  change MatrixMap.ofReferenceIsometry (W.comp V) X =
    MatrixMap.ofReferenceIsometry W (MatrixMap.ofReferenceIsometry V X)
  simp only [MatrixMap.ofReferenceIsometry_apply, ReferenceIsometry.comp,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem isometryChannel_prod (V : ReferenceIsometry a b) (W : ReferenceIsometry c d) :
    Channel.ofReferenceIsometry (V.prod W) =
      (Channel.ofReferenceIsometry V).prod (Channel.ofReferenceIsometry W) := by
  apply channel_eq_of_map_eq
  apply matrixMap_eq_of_kronecker
  intro X Y
  change MatrixMap.ofReferenceIsometry (V.prod W) (X.kronecker Y) = _
  rw [MatrixMap.ofReferenceIsometry_apply, Channel.prod_map_kronecker]
  simp only [Channel.ofReferenceIsometry_map, MatrixMap.ofReferenceIsometry_apply,
    ReferenceIsometry.prod]
  rw [show (V.matrix.kronecker W.matrix)ᴴ = V.matrixᴴ.kronecker W.matrixᴴ from
    Matrix.conjTranspose_kronecker V.matrix W.matrix]
  rw [show V.matrix.kronecker W.matrix * X.kronecker Y =
    (V.matrix * X).kronecker (W.matrix * Y) from
    (Matrix.mul_kronecker_mul V.matrix X W.matrix Y).symm]
  exact (Matrix.mul_kronecker_mul (V.matrix * X) V.matrixᴴ
    (W.matrix * Y) W.matrixᴴ).symm

theorem channel_comp_id (N : Channel a b) : N.comp (Channel.idChannel a) = N := by
  apply channel_eq_of_map_eq
  change N.map.comp (Channel.idChannel a).map = N.map
  rw [idChannel_map_eq, LinearMap.comp_id]

theorem channel_id_comp (N : Channel a b) : (Channel.idChannel b).comp N = N := by
  apply channel_eq_of_map_eq
  change (Channel.idChannel b).map.comp N.map = N.map
  rw [idChannel_map_eq, LinearMap.id_comp]

theorem isometryChannel_refl :
    Channel.ofReferenceIsometry (ReferenceIsometry.ofEquiv (Equiv.refl a)) =
      Channel.idChannel a := by
  apply channel_eq_of_map_eq
  rw [idChannel_map_eq]
  apply LinearMap.ext
  intro X
  change MatrixMap.ofReferenceIsometry (ReferenceIsometry.ofEquiv (Equiv.refl a)) X = X
  rw [MatrixMap.ofReferenceIsometry_apply]
  have hm : (ReferenceIsometry.ofEquiv (Equiv.refl a)).matrix = (1 : CMatrix a) := by
    ext i j
    rfl
  rw [hm, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- `Simulates N P` means that `P` implements `N` with an isometric encoder
and an actual channel decoder. -/
def Simulates (N : Channel a b) (P : Channel c d) : Prop :=
  ∃ V : ReferenceIsometry a c, ∃ D : Channel d b,
    D.comp (P.comp (Channel.ofReferenceIsometry V)) = N

namespace Simulates

theorem refl (N : Channel a b) : Simulates N N := by
  refine ⟨ReferenceIsometry.ofEquiv (Equiv.refl a), Channel.idChannel b, ?_⟩
  rw [isometryChannel_refl, channel_comp_id, channel_id_comp]

theorem trans {N : Channel a b} {P : Channel c d} {Q : Channel e f}
    (hNP : Simulates N P) (hPQ : Simulates P Q) : Simulates N Q := by
  obtain ⟨V, D, h⟩ := hNP
  obtain ⟨W, E, h'⟩ := hPQ
  refine ⟨W.comp V, D.comp E, ?_⟩
  rw [isometryChannel_comp]
  calc
    _ = D.comp ((E.comp (Q.comp (Channel.ofReferenceIsometry W))).comp
        (Channel.ofReferenceIsometry V)) := channel_eq_of_map_eq _ _ rfl
    _ = N := by rw [h', h]

theorem prod {N : Channel a b} {P : Channel c d} {M : Channel e f} {Q : Channel g h}
    (hNP : Simulates N P) (hMQ : Simulates M Q) : Simulates (N.prod M) (P.prod Q) := by
  obtain ⟨V, D, h⟩ := hNP
  obtain ⟨W, E, h'⟩ := hMQ
  refine ⟨V.prod W, D.prod E, ?_⟩
  rw [isometryChannel_prod, channel_prod_comp, channel_prod_comp, h, h']

theorem tensorPower {N : Channel a b} {P : Channel c d} (h : Simulates N P) :
    ∀ n : ℕ, Simulates (N.tensorPower n) (P.tensorPower n)
  | 0 => Simulates.refl _
  | n + 1 => h.prod (h.tensorPower n)

theorem exists_positive_input {N : Channel a b} {P : Channel c d}
    (h : Simulates N P) {r : Type} [Fintype r] [DecidableEq r]
    (ψ : PureVector (r × a)) (hψ : 0 < N.coherentInformationFor ψ) :
    ∃ φ : PureVector (r × c), 0 < P.coherentInformationFor φ := by
  obtain ⟨V, D, h⟩ := h
  refine ⟨V.applyPureVectorRight ψ, ?_⟩
  have hb := coherentInformationFor_decode_le (P.comp (Channel.ofReferenceIsometry V)) D ψ
  rw [h, coherentInformationFor_encode] at hb
  exact hψ.trans_le hb

end Simulates
end QuanIncapacity
