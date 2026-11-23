import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula
open Finset

namespace GlobalTheory.NefComparisonAlg

open Formalism.MainNotions.WeightThresholdDefs

theorem abs_tsum_geom_le {ι : Type*} [Finite ι] (F : ι → ℝ) (s : ℕ → ι) (a r d : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    |a * (∑' n : ℕ, r ^ (n + 1) * F (s n)) / d| ≤ ∑' n : ℕ, |a * r ^ (n + 1) * F (s n) / d| := by
  obtain ⟨M, hM⟩ := (Set.finite_range (fun i => |F i|)).bddAbove
  have hM' : ∀ i, |F i| ≤ M := fun i => hM ⟨i, rfl⟩
  have hg : Summable (fun n : ℕ => r ^ n * (|a| * r * M / |d|)) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_right _
  have hs : Summable (fun n : ℕ => ‖a * r ^ (n + 1) * F (s n) / d‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_of_nonneg hr0, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
    have h1 : 0 ≤ |a| * r ^ (n + 1) := by positivity
    calc |a| * r ^ (n + 1) * |F (s n)| ≤ |a| * r ^ (n + 1) * M :=
          mul_le_mul_of_nonneg_left (hM' _) h1
      _ = r ^ n * (|a| * r * M) := by ring
  have h := norm_tsum_le_tsum_norm hs
  simp only [Real.norm_eq_abs] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  rw [← tsum_mul_left, ← tsum_div_const]
  exact tsum_congr fun n => by ring

variable {D : D7} (V : DivX D) (P : Formalism.MainNotions.DIV.Align.PrinLev V)

end GlobalTheory.NefComparisonAlg
