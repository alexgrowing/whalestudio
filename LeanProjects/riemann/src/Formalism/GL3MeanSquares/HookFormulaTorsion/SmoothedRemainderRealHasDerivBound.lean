import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

namespace Formalism.HermitianLattices.GL2PrimeSums

theorem weighted_sum_tendsto : WeightedSumTendsto := by
  intro a S hS y hy
  set M := ⌊y⌋₊ with hM
  let g : ℕ → ℂ := fun n => a n * ((min 1 (y / (n : ℝ)) : ℝ) : ℂ) - (y : ℂ) * (a n / (n : ℂ))
  have hg0 : ∀ n : ℕ, M < n → g n = 0 := by
    intro n hn
    have hyn : y < n := (Nat.floor_lt (by linarith)).mp hn
    have hn0 : (0:ℝ) < n := by linarith
    have : min 1 (y / (n:ℝ)) = y / n := min_eq_right ((div_le_one hn0).mpr hyn.le)
    simp only [g, this]; push_cast; ring
  have hg1 : ∀ n : ℕ, 1 ≤ n → n ≤ M → g n = - (a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ)) := by
    intro n h1 hn
    have hyn : (n:ℝ) ≤ y := (Nat.le_floor_iff (by linarith)).mp hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast h1
    have : min 1 (y / (n:ℝ)) = 1 := min_eq_left ((one_le_div hn0).mpr hyn)
    simp only [g, this]; push_cast; ring
  have key : ∀ N : ℕ, M ≤ N → ∑ n ∈ Icc 1 N, a n * ((min 1 (y / (n : ℝ)) : ℝ) : ℂ)
      = (∑ n ∈ Icc 1 M, g n) + (y : ℂ) * ∑ n ∈ Icc 1 N, a n / (n : ℂ) := by
    intro N hN
    have h1 : ∑ n ∈ Icc 1 M, g n = ∑ n ∈ Icc 1 N, g n := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN)
      intro n hn hn'
      apply hg0
      by_contra hc
      exact hn' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, not_lt.mp hc⟩)
    rw [h1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _; simp only [g]; ring
  have hlim : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 M, g n) + (y : ℂ) * ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop
      (𝓝 ((∑ n ∈ Icc 1 M, g n) + (y : ℂ) * S)) := (hS.const_mul _).const_add _
  have hval : -Gchi a S y = (∑ n ∈ Icc 1 M, g n) + (y : ℂ) * S := by
    unfold Gchi
    rw [Finset.sum_congr rfl (fun n hn => hg1 n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2),
      Finset.sum_neg_distrib]
    ring
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  exact (key N hN).symm

end Formalism.HermitianLattices.GL2PrimeSums
