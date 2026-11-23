import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Mathlib.NumberTheory.LSeries.Positivity

open UpperTheory.ConvolutionTheory.RankTwoDescent

open scoped ComplexOrder

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.landau_of :
    Landau := by
  intro b hb0 hb1 hbs hent
  obtain ⟨F, hF, hFb⟩ := hent
  by_contra hinf
  have hinf' : ({n | 1 ≤ b n} \ {0, 1} : Set ℕ).Infinite :=
    Set.Infinite.diff hinf (Set.toFinite _)
  obtain ⟨m, hm⟩ := exists_nat_gt (F 0).re
  obtain ⟨S, hSsub, hScard⟩ := hinf'.exists_subset_card_eq m
  have hS0 : ∀ n ∈ S, n ≠ 0 := fun n hn h => (hSsub hn).2 (by simp [h])
  have hS1 : 1 ∉ S := fun hn => (hSsub hn).2 (by simp)
  have hS2 : ∀ n ∈ S, 1 ≤ b n := fun n hn => (hSsub hn).1
  let a : ℕ → ℂ := fun n => if n ∈ S then 0 else b n
  let G : ℂ → ℂ := fun s => F s - ∑ n ∈ S, b n / (n : ℂ) ^ s
  have hG : Differentiable ℂ G := by
    refine hF.sub (Differentiable.fun_sum fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hS0 n hn)
    exact (differentiable_const _).div (differentiable_id.const_cpow (Or.inl hn0))
      fun s => by simp [Complex.cpow_eq_zero_iff, hn0]
  have hsum : ∀ s : ℂ, 4 < s.re →
      HasSum (LSeries.term a s) (LSeries b s - ∑ n ∈ S, b n / (n : ℂ) ^ s) := by
    intro s hs
    have h1 : HasSum (LSeries.term b s) (LSeries b s) := (hbs s hs).LSeriesHasSum
    have h2 : HasSum (fun n => if n ∈ S then LSeries.term b s n else 0)
        (∑ n ∈ S, b n / (n : ℂ) ^ s) := by
      have h3 : HasSum (fun n => if n ∈ S then LSeries.term b s n else 0)
          (∑ n ∈ S, if n ∈ S then LSeries.term b s n else 0) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
      have h5 : (∑ n ∈ S, if n ∈ S then LSeries.term b s n else 0) =
          ∑ n ∈ S, b n / (n : ℂ) ^ s :=
        Finset.sum_congr rfl fun n hn => by
          simp [hn, LSeries.term_of_ne_zero (hS0 n hn)]
      rwa [h5] at h3
    have h6 : LSeries.term a s =
        fun n => LSeries.term b s n - if n ∈ S then LSeries.term b s n else 0 := by
      funext n
      by_cases hn : n ∈ S
      · simp [a, hn, LSeries.term_def]
      · simp [a, hn, LSeries.term_def]
    rw [h6]
    exact h1.sub h2
  have ha0 : 0 ≤ a := by
    intro n
    by_cases hn : n ∈ S
    · simp [a, hn]
    · simpa [a, hn] using hb0 n
  have ha1 : 0 < a 1 := by
    simp [a, hS1, hb1]
  have habs : LSeries.abscissaOfAbsConv a ≤ (4 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hsum y (by simpa using hy)).summable
  have hEq : {s : ℂ | (4 : ℝ) < s.re}.EqOn G (LSeries a) := by
    intro s hs
    have hs' : (4 : ℝ) < s.re := hs
    have h4 : (4 : ℝ) < s.re := hs'
    have : LSeries a s = LSeries b s - ∑ n ∈ S, b n / (n : ℂ) ^ s :=
      LSeriesHasSum.LSeries_eq (hsum s h4)
    simp only [G, hFb s h4]
    exact this.symm
  have hpos := LSeries.positive_of_differentiable_of_eqOn ha0 ha1 hG habs hEq 0
  have hG0 : G ((0 : ℝ) : ℂ) = F 0 - ∑ n ∈ S, b n := by
    simp [G]
  rw [hG0] at hpos
  have hre : (∑ n ∈ S, b n).re < (F 0).re := by
    have := (Complex.lt_def.mp hpos).1
    simpa using this
  have hcard : (m : ℝ) ≤ (∑ n ∈ S, b n).re := by
    rw [Complex.re_sum, ← hScard]
    have : ∀ n ∈ S, (1 : ℝ) ≤ (b n).re := fun n hn => by
      simpa using (Complex.le_def.mp (hS2 n hn)).1
    simpa using Finset.card_nsmul_le_sum S _ 1 this
  linarith
