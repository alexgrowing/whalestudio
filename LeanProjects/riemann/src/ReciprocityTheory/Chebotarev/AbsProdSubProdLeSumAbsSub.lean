import Mathlib

open Finset

namespace ReciprocityTheory.Cheb

noncomputable def tent (t : ℝ) : ℝ := max 0 (1 - |t|)

theorem tent_nonneg (t : ℝ) : 0 ≤ tent t := le_max_left _ _

theorem tent_le_one (t : ℝ) : tent t ≤ 1 :=
  max_le zero_le_one (by linarith [abs_nonneg t])

theorem tent_of_abs_le {t : ℝ} (h : |t| ≤ 1) : tent t = 1 - |t| :=
  max_eq_right (by linarith)

theorem tent_of_one_le_abs {t : ℝ} (h : 1 ≤ |t|) : tent t = 0 :=
  max_eq_left (by linarith)

theorem abs_tent_sub_tent_le (s t : ℝ) : |tent s - tent t| ≤ |s - t| := by
  unfold tent
  calc |max 0 (1 - |s|) - max 0 (1 - |t|)| ≤ |(1 - |s|) - (1 - |t|)| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ = |(|t| - |s|)| := by ring_nf
    _ ≤ |t - s| := abs_abs_sub_abs_le_abs_sub t s
    _ = |s - t| := abs_sub_comm t s

theorem abs_lt_one_of_tent_ne_zero {t : ℝ} (h : tent t ≠ 0) : |t| < 1 := by
  by_contra h'
  exact h (tent_of_one_le_abs (not_lt.mp h'))

theorem tent_add_int_eq_zero_of_notMem (t : ℝ) {n : ℤ} (hn : n ∉ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ)) :
    tent (t + n) = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  apply tent_of_one_le_abs
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  rcases lt_or_gt_of_ne hn.1 with h | h
  · have : n ≤ -⌊t⌋ - 2 := by omega
    have : (n : ℝ) ≤ -⌊t⌋ - 2 := by exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith
  · have : (n : ℝ) ≥ -⌊t⌋ + 1 := by exact_mod_cast (show n ≥ -⌊t⌋ + 1 by omega)
    rw [abs_of_nonneg (by linarith)]; linarith

theorem sum_tent_add_int_pair (t : ℝ) :
    ∑ n ∈ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ), tent (t + n) = 1 := by
  have hne : (-⌊t⌋ : ℤ) ≠ -⌊t⌋ - 1 := by omega
  rw [Finset.sum_pair hne]
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  push_cast
  rw [tent_of_abs_le, tent_of_abs_le]
  · rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]; ring
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

section Product

theorem abs_prod_sub_prod_le_sum_abs_sub {κ : Type*} (s : Finset κ) (a b : κ → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj]
    have hP : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hb i (mem_insert_of_mem hi))
    have ih' := ih (fun i hi => ha i (mem_insert_of_mem hi)) (fun i hi => hb i (mem_insert_of_mem hi))
    have haj := ha j (mem_insert_self j s)
    have hsum : 0 ≤ ∑ i ∈ s, |a i - b i| := sum_nonneg fun i _ => abs_nonneg _
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i| := by ring_nf
      _ ≤ |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a j - b j| * |∏ i ∈ s, b i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ∑ i ∈ s, |a i - b i| + |a j - b j| * 1 :=
        add_le_add (mul_le_mul haj ih' (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
      _ = |a j - b j| + ∑ i ∈ s, |a i - b i| := by ring

variable {ι : Type*} [Fintype ι]

noncomputable def Tent (y : ι → ℝ) : ℝ := ∏ i, tent (y i)

theorem Tent_nonneg (y : ι → ℝ) : 0 ≤ Tent y := prod_nonneg fun _ _ => tent_nonneg _

theorem Tent_le_one (y : ι → ℝ) : Tent y ≤ 1 :=
  prod_le_one (fun _ _ => tent_nonneg _) (fun _ _ => tent_le_one _)

theorem abs_lt_one_of_Tent_ne_zero {y : ι → ℝ} (h : Tent y ≠ 0) (i : ι) : |y i| < 1 :=
  abs_lt_one_of_tent_ne_zero fun h' => h (prod_eq_zero (mem_univ i) h')

theorem abs_Tent_sub_Tent_le (y y' : ι → ℝ) : |Tent y - Tent y'| ≤ ∑ i, |y i - y' i| := by
  unfold Tent
  refine (abs_prod_sub_prod_le_sum_abs_sub univ _ _ (fun i _ => ?_) (fun i _ => ?_)).trans
    (sum_le_sum fun i _ => abs_tent_sub_tent_le (y i) (y' i))
  · rw [abs_of_nonneg (tent_nonneg _)]; exact tent_le_one _
  · rw [abs_of_nonneg (tent_nonneg _)]; exact tent_le_one _

theorem Tent_add_int_eq_zero_of_notMem [DecidableEq ι] (y : ι → ℝ) {n : ι → ℤ}
    (hn : n ∉ Fintype.piFinset fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) :
    Tent (fun i => y i + n i) = 0 := by
  rw [Fintype.mem_piFinset] at hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  exact prod_eq_zero (mem_univ i) (tent_add_int_eq_zero_of_notMem (y i) hi)

theorem sum_Tent_add_int_piFinset [DecidableEq ι] (y : ι → ℝ) :
    ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Tent (fun i => y i + n i) = 1 := by
  classical
  show ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), ∏ i, tent (y i + n i) = 1
  rw [← Finset.prod_univ_sum (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) (fun i n => tent (y i + n))]
  exact prod_eq_one fun i _ => sum_tent_add_int_pair (y i)

theorem hasSum_Tent_add_int (y : ι → ℝ) : HasSum (fun n : ι → ℤ => Tent (fun i => y i + n i)) 1 := by
  classical
  have h : HasSum (fun n : ι → ℤ => Tent (fun i => y i + n i))
      (∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Tent (fun i => y i + n i)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => Tent_add_int_eq_zero_of_notMem y hn
  rwa [sum_Tent_add_int_piFinset] at h

end Product

end ReciprocityTheory.Cheb
