import QuanIncapacity.Qutrit.Defect

/-! Every individual entry in the manuscript's nine-contraction table.
The input matrix is arbitrary complex, including non-Hermitian cross terms. -/

noncomputable section
open QIT
open scoped Matrix BigOperators

namespace QuanIncapacity.DefectContractions

def part (s μ : Fin 3) : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ := Matrix.of fun p i ↦
  if s = 0 then (if p.1 = i then 1 else 0 : ℂ) * (if p.2 = μ then 1 else 0)
  else if s = 1 then (1 / 2 : ℂ) * (if p.1 = μ then 1 else 0) * (if p.2 = i then 1 else 0)
  else -(1 / 2 : ℂ) * (if μ = i then 1 else 0) * (if p.1 = p.2 then 1 else 0)

def entry (s t : Fin 3) (τ : CMatrix (Fin 3)) : CMatrix (Fin 3 × Fin 3) :=
  Matrix.of fun jk pq ↦
    if s = 0 then
      if t = 0 then (if jk.2 = pq.2 then 1 else 0 : ℂ) * τ jk.1 pq.1
      else if t = 1 then (1 / 2 : ℂ) * (if jk.2 = pq.1 then 1 else 0) * τ jk.1 pq.2
      else -(1 / 2 : ℂ) * (if pq.1 = pq.2 then 1 else 0) * τ jk.1 jk.2
    else if s = 1 then
      if t = 0 then (1 / 2 : ℂ) * (if jk.1 = pq.2 then 1 else 0) * τ jk.2 pq.1
      else if t = 1 then (1 / 4 : ℂ) * (if jk.1 = pq.1 then 1 else 0) * τ jk.2 pq.2
      else -(1 / 4 : ℂ) * (if pq.1 = pq.2 then 1 else 0) * τ jk.2 jk.1
    else
      if t = 0 then -(1 / 2 : ℂ) * (if jk.1 = jk.2 then 1 else 0) * τ pq.2 pq.1
      else if t = 1 then -(1 / 4 : ℂ) * (if jk.1 = jk.2 then 1 else 0) * τ pq.1 pq.2
      else (1 / 4 : ℂ) * (if jk.1 = jk.2 then 1 else 0) *
        (if pq.1 = pq.2 then 1 else 0) * τ.trace

set_option maxHeartbeats 4000000 in
theorem table (s t : Fin 3) (τ : CMatrix (Fin 3)) :
    ∑ μ : Fin 3, part s μ * τ * (part t μ).conjTranspose = entry s t τ := by
  ext ⟨j, k⟩ ⟨p, q⟩
  fin_cases s <;> fin_cases t <;> fin_cases j <;> fin_cases k <;> fin_cases p <;> fin_cases q <;>
    norm_num [part, entry, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.trace, Fintype.sum_prod_type, map_ofNat]
  all_goals ring

theorem G_sum (μ : Fin 3) : G μ = ∑ s : Fin 3, part s μ := by
  ext p i
  simp [G, part, Fin.sum_univ_succ]
  split_ifs <;> ring

end QuanIncapacity.DefectContractions
