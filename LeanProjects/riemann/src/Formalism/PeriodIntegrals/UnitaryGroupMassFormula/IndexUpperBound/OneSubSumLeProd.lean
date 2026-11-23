import Mathlib
import Formalism.PeriodIntegrals.IndexUBound

namespace PI.UnitaryGroupMassFormula.IndexUBound

open Finset

theorem one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (P b : ι → ℝ)
    (hP0 : ∀ i ∈ s, 0 ≤ P i) (hP1 : ∀ i ∈ s, P i ≤ 1) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hPb : ∀ i ∈ s, 1 - b i ≤ P i) : 1 - ∑ i ∈ s, b i ≤ ∏ i ∈ s, P i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hm : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have hQ0 : 0 ≤ ∏ i ∈ s, P i := Finset.prod_nonneg fun i hi => hP0 i (hm i hi)
    have hQ1 : ∏ i ∈ s, P i ≤ 1 :=
      Finset.prod_le_one (fun i hi => hP0 i (hm i hi)) (fun i hi => hP1 i (hm i hi))
    have h := ih (fun i hi => hP0 i (hm i hi)) (fun i hi => hP1 i (hm i hi))
      (fun i hi => hb i (hm i hi)) (fun i hi => hPb i (hm i hi))
    have ha1 := hP1 a (Finset.mem_insert_self a s)
    have hab := hPb a (Finset.mem_insert_self a s)
    nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hQ1)]

theorem prod_Ico_pow (g : ℝ) (r : ℕ) :
    ∏ i ∈ Ico 1 r, g ^ i = g ^ (r * (r - 1) / 2) := by
  rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_range_id]
  congr 1
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hr]
    simp

theorem prod_factor (g : ℝ) (hg : g ≠ 0) (r : ℕ) :
    ∏ i ∈ Ico 1 r, (g ^ i - 1) = g ^ (r * (r - 1) / 2) * ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) := by
  rw [← PI.UnitaryGroupMassFormula.IndexUBound.prod_Ico_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_sub, mul_one, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hg)]

theorem inner_bounds (g : ℝ) (hg : 2 ≤ g) (r : ℕ) :
    0 ≤ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) ∧ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) ≤ 1 ∧
      1 - 1 / (g - 1) ≤ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) := by
  have hg0 : 0 < g := by linarith
  set x := g⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hg0
  have hx1 : x ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hxg : x * g = 1 := inv_mul_cancel₀ hg0.ne'
  have hpow0 : ∀ i : ℕ, 0 ≤ x ^ i := fun i => pow_nonneg hx0.le i
  have hpow1 : ∀ i : ℕ, x ^ i ≤ 1 := fun i => pow_le_one₀ hx0.le hx1
  have hf0 : ∀ i ∈ Ico 1 r, 0 ≤ 1 - x ^ i := fun i _ => sub_nonneg.2 (hpow1 i)
  have hf1 : ∀ i ∈ Ico 1 r, 1 - x ^ i ≤ 1 := fun i _ => by linarith [hpow0 i]
  refine ⟨Finset.prod_nonneg hf0, Finset.prod_le_one hf0 hf1, ?_⟩
  have hS : (∑ i ∈ Ico 1 r, x ^ i) * (g - 1) ≤ 1 := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · have h := geom_sum_Ico_mul x hr
      have e : (∑ i ∈ Ico 1 r, x ^ i) * (g - 1) = 1 - x ^ r * g := by
        linear_combination (-g) * h + ((∑ i ∈ Ico 1 r, x ^ i) + 1) * hxg
      rw [e]
      nlinarith [hpow0 r]
  have hS' : ∑ i ∈ Ico 1 r, x ^ i ≤ 1 / (g - 1) := by
    rw [le_div_iff₀ (by linarith)]
    exact hS
  have h1 := PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod (Ico 1 r) (fun i => 1 - x ^ i)
    (fun i => x ^ i) hf0 hf1 (fun i _ => hpow0 i) (fun i _ => le_refl _)
  beta_reduce at h1
  linarith

end PI.UnitaryGroupMassFormula.IndexUBound
