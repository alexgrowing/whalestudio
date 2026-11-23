import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedShellFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuation

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LFGInt

open Ad3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem summable_cut {p r C B : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun k : ℤ => ‖(((if p ^ k ≤ B then C * r ^ k else 0 : ℝ) : ℂ))‖ := by
  set f : ℤ → ℝ := fun k => ‖(((if p ^ k ≤ B then C * r ^ k else 0 : ℝ) : ℂ))‖ with hf
  have hpos : Summable fun n : ℕ => f n := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left |C|)
    simp only [hf]
    split_ifs
    · simp [abs_mul, abs_of_pos hr0]
    · simp only [Complex.ofReal_zero, norm_zero]
      positivity
  have hneg : Summable fun n : ℕ => f (-(n : ℤ)) := by
    have ht := tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hp0 |>.mpr hp1)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_gt_atTop B))
    refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
    have hn' : N ≤ n := by simpa using hn
    have hB : ¬ p ^ (-(n : ℤ)) ≤ B := by
      rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
      exact not_le.mpr (hN n hn')
    simp only [hf, if_neg hB, Complex.ofReal_zero, norm_zero]
  exact Summable.of_nat_of_neg hpos hneg

variable [MeasurableSpace F] [BorelSpace F]

end GlobalTheory.CompanionTheory.LFGInt
