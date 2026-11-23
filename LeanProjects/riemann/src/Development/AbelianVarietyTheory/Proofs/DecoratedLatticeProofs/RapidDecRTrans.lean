import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RTransDecay

theorem rapidDec_rTrans : ∀ (D : D7) (V : HSp D) (G : GA D V → ℂ), RapidDec V G → (∀ h, RapidDec V (rTrans h G)) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ g h, ‖G (g * h)‖ * quotHeight V g ^ N ≤ C * height V h ^ N := by
  intro D V G hG
  refine ⟨fun h => hG.mul_right h, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hG.decay N
  refine ⟨C, fun g h => ?_⟩
  have h1 : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h := by
    simpa using GlobalTheory.Grow.quotHeight_mul_le V (g * h) h⁻¹
  calc ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V g ^ N
        ≤ ‖G (g * h)‖ * (GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (GlobalTheory.Grow.quotHeight_pos V g).le h1 N) (norm_nonneg _)
    _ = ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V (g * h) ^ N * GlobalTheory.Grow.height V h ^ N := by ring
    _ ≤ C * GlobalTheory.Grow.height V h ^ N := mul_le_mul_of_nonneg_right (hC _) (pow_pos (GlobalTheory.Grow.height_pos V h) N).le

end GlobalTheory.RTransDecay
