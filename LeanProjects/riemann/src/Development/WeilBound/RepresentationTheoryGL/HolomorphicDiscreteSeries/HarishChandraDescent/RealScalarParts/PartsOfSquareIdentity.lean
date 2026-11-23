import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3.RealScalarQuadraticForm

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M}

theorem re_smul_self (κ : ℝ) (y : M) : (⟪(κ : ℂ) • y, y⟫_ℂ).re = κ * ‖y‖ ^ 2 := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem norm_smul_sq (c : ℝ) (y : M) : ‖(c : ℂ) • y‖ ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem pt {ν μ : Fin n → ℝ} {y : M} (hwt : IsWt E ν y) (a b : Fin n) :
    ‖E a b y - (if a = b then (μ a : ℂ) else 0) • y‖ ^ 2 =
      ‖E a b y‖ ^ 2 + if a = b then ((ν a - μ a) ^ 2 - ν a ^ 2) * ‖y‖ ^ 2 else 0 := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, if_pos rfl, hwt a, ← sub_smul, ← Complex.ofReal_sub, norm_smul_sq, norm_smul_sq]
    ring
  · rw [if_neg h, if_neg h, zero_smul, sub_zero, add_zero]

theorem qf_eq {ν μ : Fin n → ℝ} {y : M} (hwt : IsWt E ν y) :
    qf E μ y = ∑ a, ∑ b, ‖E a b y‖ ^ 2 + (nsq (ν - μ) - nsq ν) * ‖y‖ ^ 2 := by
  unfold qf
  simp only [pt hwt, sum_add_distrib, sum_ite_eq, mem_univ, if_true]
  congr 1
  simp only [nsq, dot, Pi.sub_apply, ← sum_sub_distrib, sum_mul]
  exact sum_congr rfl fun a _ => by ring

theorem split_sum (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, f a b = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), f a b +
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), f a b := by
  rw [← sum_add_distrib]
  exact sum_congr rfl fun a _ => (sum_filter_add_sum_filter_not univ (fun b => ε b = ε a) (f a)).symm

theorem diag_le {ν : Fin n → ℝ} {y : M} (hwt : IsWt E ν y) :
    nsq ν * ‖y‖ ^ 2 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b y‖ ^ 2 := by
  have h1 : nsq ν * ‖y‖ ^ 2 = ∑ a, ‖E a a y‖ ^ 2 := by
    simp only [nsq, dot, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [hwt a, norm_smul_sq]; ring
  rw [h1]
  refine sum_le_sum fun a _ => ?_
  exact single_le_sum (f := fun b => ‖E a b y‖ ^ 2) (fun _ _ => by positivity) (mem_filter.2 ⟨mem_univ a, rfl⟩)

end PositivityTheory.RgHe3.RealScalarQuadraticForm

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

theorem parts_of_square_identity : SqId → Parts := by
  intro hsq n ε M _ _ E hG hU μ ν κ S y hg hq
  obtain ⟨h1, h2, -⟩ := hsq n ε M E hG hU y
  rw [hg.cas, RealScalarQuadraticForm.re_smul_self] at h1 h2
  have hqf := RealScalarQuadraticForm.qf_eq (μ := μ) hg.wt
  rw [RealScalarQuadraticForm.split_sum (ε := ε)] at hqf
  have hd := RealScalarQuadraticForm.diag_le (ε := ε) hg.wt
  have hD : 0 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), ‖E a b y‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  have hN : 0 ≤ nsq (ν - μ) := by
    unfold nsq dot
    exact Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have hy : 0 < ‖y‖ ^ 2 := by
    have := norm_pos_iff.2 hg.ne
    positivity
  refine ⟨?_, ?_, ?_⟩
  · refine le_of_mul_le_mul_right ?_ hy
    nlinarith
  · refine le_of_mul_le_mul_right ?_ hy
    nlinarith
  · nlinarith
end PositivityTheory.RgHe3
