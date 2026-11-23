import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepIteratedQuotientIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftConvContGrowth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_double_step_iterated_quotient_integral : ∀ (D : D7) (c : Comm D) (t : Tup c), DoubleStep D → c.Is → t.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ), (∀ a, IsContAut (c.X j) (φ a)) → RapidDec _ f → RapidDec _ (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) → ∃ F₁ : GA D (c.V (j + 1)) → ℂ, IsQuotIntL1 (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ F₁ (t.perF j (σ + 1) h φ (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁))) ∧ ∀ h₁, IsQuotIntL1 (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ (t.integrand j σ h P₁ P₂ φ f h₁) (F₁ h₁) := by
  first | exact @GlobalTheory.SeeSaw.Assemble.doubleStep_tuple | exact GlobalTheory.SeeSaw.Assemble.doubleStep_tuple | (intros; apply GlobalTheory.SeeSaw.Assemble.doubleStep_tuple <;> assumption)
