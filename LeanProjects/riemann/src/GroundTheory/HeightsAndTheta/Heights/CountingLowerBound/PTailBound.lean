import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory

universe u

theorem TailBound.proof (h1 : MeanCountBound.Statement.{u}) :
    TailBound.Statement.{u} := by
  intro X _ μ lam cnt a ka r hH x hx
  have hprob := hH.isProbability
  set t := exp (-x) * r with ht_def
  have ht_pos : 0 < t := mul_pos (exp_pos _) hH.r_pos
  have ht_le : t ≤ r := by
    have : exp (-x) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith [hH.r_pos]
  have hS : MeasurableSet {z | lam z < t} := measurableSet_lt hH.lam_meas measurable_const

  have hmarkov : μ.real {z | lam z < t} ≤ meanCount μ cnt t := by
    rw [← integral_indicator_one hS, meanCount]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hS) (hH.integrable t ht_pos) ?_
    intro z
    by_cases hz : z ∈ {z | lam z < t}
    · rw [Set.indicator_of_mem hz]
      exact hH.one t ht_pos ht_le z hz
    · rw [Set.indicator_of_notMem hz]
      exact hH.cnt_nonneg t z

  have hscale : meanCount μ cnt t = exp (-x) ^ ka * meanCount μ cnt r :=
    hH.scaling (exp (-x)) r (exp_pos _) hH.r_pos
  have hpow : exp (-x) ^ ka = exp (-(ka * x)) := by
    rw [← exp_mul]; ring_nf
  have hmean := h1 X μ lam cnt a ka r hH
  have hbound : μ.real {z | lam z < t} ≤ 2 * 36 ^ a * exp (-(ka * x)) := by
    calc μ.real {z | lam z < t} ≤ meanCount μ cnt t := hmarkov
      _ = exp (-(ka * x)) * meanCount μ cnt r := by rw [hscale, hpow]
      _ ≤ exp (-(ka * x)) * (2 * 36 ^ a) :=
          mul_le_mul_of_nonneg_left hmean (exp_pos _).le
      _ = 2 * 36 ^ a * exp (-(ka * x)) := by ring
  have hone : μ.real {z | lam z < t} ≤ 1 := measureReal_le_one
  exact le_min hone hbound

end GroundTheory.Heights₂.Heights.LowerBound
