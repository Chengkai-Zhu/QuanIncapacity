import QuanIncapacity.Activation.DephasedErasure
import QuanIncapacity.Framework.ChannelMixture

/-! The dephased-erasure formula is CPTP for every `q, η ∈ [0,1]`, including
all endpoints. -/

noncomputable section
open QIT
open scoped ComplexOrder MatrixOrder

namespace QuanIncapacity.DephasedErasure

variable {a : Type} [Fintype a] [DecidableEq a]

def transmitted : Channel a (Option a) :=
  Channel.ofReferenceIsometry (ReferenceIsometry.ofInjective some (Option.some_injective a))

def dephased : Channel a (Option a) := Channel.prepare (fun i ↦ basisState (some i))

def erased : Channel a (Option a) := Channel.prepare (fun _ ↦ basisState none)

def channel (q η : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    Channel a (Option a) :=
  channelMix q hq0 hq1 (channelMix η hη0 hη1 transmitted dephased) erased

theorem transmitted_single (i j : a) :
    (transmitted (a := a)).map (Matrix.single i j 1) = Matrix.single (some i) (some j) 1 :=
  MatrixMap.ofReferenceIsometry_ofInjective_single some (Option.some_injective a) i j

theorem dephased_single (i j : a) : (dephased (a := a)).map (Matrix.single i j 1) =
    if i = j then Matrix.single (some i) (some i) 1 else 0 := by
  change Channel.prepareMap _ _ = _
  rw [Channel.prepareMap_single, basisState_matrix]

theorem erased_single (i j : a) : (erased (a := a)).map (Matrix.single i j 1) =
    if i = j then Matrix.single none none 1 else 0 := by
  change Channel.prepareMap _ _ = _
  rw [Channel.prepareMap_single, basisState_matrix]

theorem channel_map (q η : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (channel (a := a) q η hq0 hq1 hη0 hη1).map = map q η := by
  have hs (i j : a) : (channel q η hq0 hq1 hη0 hη1).map (Matrix.single i j 1) =
      map q η (Matrix.single i j 1) := by
    change (channelMix q hq0 hq1 (channelMix η hη0 hη1 transmitted dephased) erased).map _ = _
    rw [channelMix_map, channelMix_map, transmitted_single, dephased_single, erased_single]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, if_pos rfl, map_diagonal]
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
        Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · rw [if_neg hij, if_neg hij, map_off_diagonal q η i j hij]
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
        Matrix.zero_apply, mul_zero, add_zero]
      ring
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single (channel q η hq0 hq1 hη0 hη1).map X,
    MatrixMap.map_eq_sum_single (map q η) X]
  simp only [hs]

end QuanIncapacity.DephasedErasure
