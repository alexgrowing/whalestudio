import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Gelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.GelfandSeries

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def hwShift (ν : Fin n → ℝ) : Fin n → ℂ := fun r => ((ν r : ℝ) : ℂ) + (((n - 1 - (r : ℕ) : ℕ) : ℝ) : ℂ)

theorem hwShift_eq_icShift (ν : Fin n → ℝ) : hwShift ν = icShift (ν + rho n) := by
  funext r
  have hr := r.isLt
  simp only [hwShift, icShift, rho, Pi.add_apply]
  rw [Nat.cast_sub (by omega : (r : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem ePow_hw_lower {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) (s r : Fin n) (hsr : s < r) : ePow E k s r v = 0 := by
  induction k generalizing s r with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, hsr.ne]
  | succ k ih =>
    rw [show ePow E (k + 1) s r = ∑ c, E s c * ePow E k c r from by simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply], LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro c _
    rw [Module.End.mul_apply]
    rcases lt_or_ge c r with hcr | hrc
    · rw [ih c r hcr, map_zero]
    · have hc := ePow_comm hE k s c c r
      rw [if_pos rfl, if_neg hsr.ne'] at hc
      have hc' := congrArg (fun f => f v) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply, sub_zero] at hc'
      rw [hv.2 s c (lt_of_lt_of_le hsr hrc), map_zero, sub_zero, ih s r hsr] at hc'
      exact hc'

theorem ePow_hw_diag {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) (r : Fin n) : ePow E k r r v = gx (hwShift ν) k r • v := by
  induction k generalizing r with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, gx]
  | succ k ih =>
    have key : ∀ c, E r c (ePow E k c r v) =
        ((if c = r then (ν r : ℂ) * gx (hwShift ν) k r else 0) +
         (if r < c then gx (hwShift ν) k r - gx (hwShift ν) k c else 0)) • v := by
      intro c
      rcases lt_trichotomy c r with h | h | h
      · rw [ePow_hw_lower hE hv k c r h, map_zero, if_neg h.ne, if_neg (not_lt.2 h.le)]
        simp
      · subst h
        rw [ih, LinearMap.map_smul, hv.1, smul_smul, if_pos rfl, if_neg (lt_irrefl _), add_zero,
          mul_comm]
      · have hc := ePow_comm hE k r c c r
        rw [if_pos rfl, if_pos rfl] at hc
        have hc' := congrArg (fun f => f v) hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc'
        rw [hv.2 r c h, map_zero, sub_zero, ih, ih c] at hc'
        rw [if_neg h.ne', if_pos h, zero_add, sub_smul]
        exact hc'
    rw [show ePow E (k + 1) r r = ∑ c, E r c * ePow E k c r from by simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply], LinearMap.sum_apply]
    simp only [Module.End.mul_apply, key]
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← Finset.sum_filter,
      Finset.sum_sub_distrib, Finset.sum_const]
    have hf : (univ.filter fun c => r < c) = Finset.Ioi r := by ext; simp
    rw [hf, Fin.card_Ioi, nsmul_eq_mul]
    simp only [gx, hwShift, hf]
    push_cast
    ring

theorem gelfand_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) : gelfand E k v = gval (icShift (ν + rho n)) k • v := by
  unfold gelfand
  rw [LinearMap.sum_apply]
  simp only [ePow_hw_diag hE hv k, ← Finset.sum_smul, sum_gx_eq_gval, hwShift_eq_icShift]

end ReciprocityTheory.ChartRestriction.DS
