import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaIntLeSetLIntegralOfCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absThetaInt_le_setLIntegral_of_cover' : ∀ (D : D7) (V : HSp D) (n : ℕ) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank n → ℂ, Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → GlobalTheory.SiegelFormula.absThetaInt V ν φ ≤ ∫⁻ g in S, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
  first | exact @GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover | exact GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover | (intros; apply GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover <;> assumption)
