import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBoxStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSupBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section
namespace GlobalTheory.MixSumBound

theorem ofReal_quotHeight_pow {D : D7} (T : HSp D) (A : ℕ) (h : GA D T) :
    ENNReal.ofReal (quotHeight T h ^ A) = ⨅ γ : GQ T, ENNReal.ofReal (height T (γ * h) ^ A) := by
  set φ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (max t 1 ^ A) with hφ
  have hmono : Monotone φ := fun a b hab =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (zero_le_one.trans (le_max_right _ _)) (max_le_max hab le_rfl) A)
  have hcont : Continuous φ := ENNReal.continuous_ofReal.comp ((continuous_id.max continuous_const).pow A)
  have hbdd : BddBelow (Set.range fun γ : GQ T => height T (γ * h)) :=
    ⟨1, by rintro _ ⟨γ, rfl⟩; exact one_le_height T _⟩
  have e := Monotone.map_ciInf_of_continuousAt hcont.continuousAt hmono hbdd
  have e1 : φ (quotHeight T h) = ENNReal.ofReal (quotHeight T h ^ A) := by
    simp only [hφ, max_eq_left (one_le_quotHeight T h)]
  have e2 : ∀ γ : GQ T, φ (height T (γ * h)) = ENNReal.ofReal (height T (γ * h) ^ A) := fun γ => by
    simp only [hφ, max_eq_left (one_le_height T _)]
  rw [← e1, quotHeight, e]
  exact iInf_congr e2

end GlobalTheory.MixSumBound
