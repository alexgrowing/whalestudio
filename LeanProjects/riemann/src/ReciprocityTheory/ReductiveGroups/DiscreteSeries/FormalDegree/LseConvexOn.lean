import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.EigenvectorUnitaryMulStar

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

section LSE

variable {ι : Type*} [Fintype ι]

theorem lse_pos (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (t : ℝ) :
    0 < ∑ i, w i * Real.exp (t * y i) := by
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push_neg at h
    have h0 : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hw0 i))
    linarith
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw0 j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

theorem lse_convexOn (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ i, w i * Real.exp (t * y i))) := by
  refine ⟨convex_univ, fun t1 _ t2 _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set A := ∑ i, w i * Real.exp (t1 * y i) with hA
  set B := ∑ i, w i * Real.exp (t2 * y i) with hB
  have hA0 : 0 < A := lse_pos w y hw0 hw1 t1
  have hB0 : 0 < B := lse_pos w y hw0 hw1 t2
  set E := Real.exp (a * Real.log A + b * Real.log B) with hE
  have key : ∀ i, Real.exp ((a * t1 + b * t2) * y i) ≤
      (a * (Real.exp (t1 * y i) / A) + b * (Real.exp (t2 * y i) / B)) * E := by
    intro i
    have h1 := convexOn_exp.2 (Set.mem_univ (t1 * y i - Real.log A))
      (Set.mem_univ (t2 * y i - Real.log B)) ha hb hab
    simp only [smul_eq_mul] at h1
    have e1 : Real.exp (t1 * y i - Real.log A) = Real.exp (t1 * y i) / A := by
      rw [Real.exp_sub, Real.exp_log hA0]
    have e2 : Real.exp (t2 * y i - Real.log B) = Real.exp (t2 * y i) / B := by
      rw [Real.exp_sub, Real.exp_log hB0]
    rw [e1, e2] at h1
    have e3 : Real.exp ((a * t1 + b * t2) * y i) =
        Real.exp (a * (t1 * y i - Real.log A) + b * (t2 * y i - Real.log B)) * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hsum : ∑ i, w i * Real.exp ((a * t1 + b * t2) * y i) ≤ E := by
    calc ∑ i, w i * Real.exp ((a * t1 + b * t2) * y i)
        ≤ ∑ i, w i * ((a * (Real.exp (t1 * y i) / A) + b * (Real.exp (t2 * y i) / B)) * E) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (key i) (hw0 i))
      _ = (a * (A / A) + b * (B / B)) * E := by
          rw [hA, hB, Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
      _ = E := by rw [div_self hA0.ne', div_self hB0.ne', mul_one, mul_one, hab, one_mul]
  have hpos := lse_pos w y hw0 hw1 (a * t1 + b * t2)
  calc Real.log (∑ i, w i * Real.exp ((a * t1 + b * t2) * y i)) ≤ Real.log E :=
        Real.log_le_log hpos hsum
    _ = a * Real.log A + b * Real.log B := Real.log_exp _

theorem lse_one_le (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hw2 : ∑ i, w i * y i = 0) : 1 ≤ ∑ i, w i * Real.exp (y i) := by
  calc (1 : ℝ) = ∑ i, w i * (1 + y i) := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero]
    _ ≤ ∑ i, w i * Real.exp (y i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (by linarith [Real.add_one_le_exp (y i)]) (hw0 i))

theorem lse_upper (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hw2 : ∑ i, w i * y i = 0) (hy : ∀ i, |y i| ≤ 1) :
    Real.log (∑ i, w i * Real.exp (y i)) ≤ ∑ i, w i * y i ^ 2 := by
  have hpos : 0 < ∑ i, w i * Real.exp (y i) := by simpa using lse_pos w y hw0 hw1 1
  have hle : ∑ i, w i * Real.exp (y i) ≤ 1 + ∑ i, w i * y i ^ 2 := by
    calc ∑ i, w i * Real.exp (y i) ≤ ∑ i, w i * (1 + y i + y i ^ 2) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            (by
              have h := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hy i))
              linarith [h.2]) (hw0 i))
      _ = 1 + ∑ i, w i * y i ^ 2 := by
          simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero]
  calc Real.log (∑ i, w i * Real.exp (y i)) ≤ Real.log (1 + ∑ i, w i * y i ^ 2) :=
        Real.log_le_log hpos hle
    _ ≤ (1 + ∑ i, w i * y i ^ 2) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    _ = ∑ i, w i * y i ^ 2 := by ring

theorem lse_lower (w y : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hw2 : ∑ i, w i * y i = 0) {ep : ℝ} (he0 : 0 ≤ ep) (he1 : ep ≤ 1)
    (hy : ∀ i, |y i| ≤ ep / 2) :
    (∑ i, w i * y i ^ 2) / 2 * (1 - ep) ≤ Real.log (∑ i, w i * Real.exp (y i)) := by
  set V := ∑ i, w i * y i ^ 2 with hV
  have hD : 1 ≤ ∑ i, w i * Real.exp (y i) := lse_one_le w y hw0 hw1 hw2
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (sq_nonneg _))
  have hVle : V ≤ ep ^ 2 / 4 := by
    calc V ≤ ∑ i, w i * (ep / 2) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (hw0 i))
          have := sq_abs (y i)
          have h1 := hy i
          have h2 := abs_nonneg (y i)
          nlinarith
      _ = ep ^ 2 / 4 := by rw [← Finset.sum_mul, hw1]; ring

  have hterm : ∀ i, 1 + y i + y i ^ 2 * (1 / 2 - ep / 9) ≤ Real.exp (y i) := by
    intro i
    have hyi : |y i| ≤ 1 := (hy i).trans (by linarith)
    have hb := Real.exp_bound hyi (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have hb' := (abs_le.1 hb).1
    have hc : |y i| ^ 3 ≤ ep / 2 * y i ^ 2 := by
      have : |y i| ^ 3 = |y i| * y i ^ 2 := by rw [pow_succ, sq_abs]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)
    nlinarith
  have hlow : 1 + V * (1 / 2 - ep / 9) ≤ ∑ i, w i * Real.exp (y i) := by
    calc 1 + V * (1 / 2 - ep / 9) = ∑ i, w i * (1 + y i + y i ^ 2 * (1 / 2 - ep / 9)) := by
          simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hw2, add_zero, hV,
            Finset.sum_mul]
          refine congrArg _ (Finset.sum_congr rfl (fun i _ => by ring))
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw0 i))
  set c := V / 2 * (1 - ep) with hc
  have hc0 : 0 ≤ c := mul_nonneg (by linarith) (by linarith)
  have hc1 : c ≤ V / 2 := by nlinarith
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; nlinarith
  have hexp : Real.exp c ≤ 1 + c + c ^ 2 := by
    have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hcabs)).2
    linarith
  have hcc : c ^ 2 ≤ V * ep ^ 2 / 8 := by nlinarith
  have hfin : 1 + c + c ^ 2 ≤ ∑ i, w i * Real.exp (y i) := by
    have : c + c ^ 2 ≤ V * (1 / 2 - ep / 9) := by
      rw [hc]
      have : V * ep ^ 2 / 8 ≤ V * ep * (7 / 18) := by nlinarith
      nlinarith
    linarith
  have hpos : 0 < ∑ i, w i * Real.exp (y i) := by linarith
  rw [← Real.exp_le_exp, Real.exp_log hpos]
  linarith

end LSE

end ReciprocityTheory.ChartRestriction.DS
