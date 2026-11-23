import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingGrowthExponent
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothing_norm_le_height_pow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ (f : GA E a → ℂ) (C : ℝ) (N : ℕ), (∀ y, ‖f (infGL E a y)‖ ≤ C * height y ^ N) → ∃ C' : ℝ, ∀ y, ‖smoothing ν α f (infGL E a y)‖ ≤ C' * height y ^ N := by
  first | exact @GlobalTheory.AutGrowth.smoothing_growth_exponent | exact GlobalTheory.AutGrowth.smoothing_growth_exponent | (intros; apply GlobalTheory.AutGrowth.smoothing_growth_exponent <;> assumption)
