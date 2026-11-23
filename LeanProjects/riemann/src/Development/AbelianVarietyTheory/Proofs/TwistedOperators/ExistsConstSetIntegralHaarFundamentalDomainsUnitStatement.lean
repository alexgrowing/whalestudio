import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSetIntegralHaarFundamentalDomainsUnit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_setIntegral_haar_fundamentalDomains_unitary : ∀ {D : D7} {V : HSp D} (ν₁ ν₂ : Measure (GA D V)) (fd₁ fd₂ : Set (GA D V)), ν₁.IsHaarMeasure → ν₂.IsHaarMeasure → IsFundamentalDomain (GQ V) fd₁ ν₁ → IsFundamentalDomain (GQ V) fd₂ ν₂ → ∃ c : ℂ, ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (IntegrableOn f fd₁ ν₁ ↔ IntegrableOn f fd₂ ν₂) ∧ ∫ g in fd₁, f g ∂ν₁ = c * ∫ g in fd₂, f g ∂ν₂ := by
  first | exact @GlobalTheory.HaarFundDom.setIntegral_eq_const_mul | exact GlobalTheory.HaarFundDom.setIntegral_eq_const_mul | (intros; apply GlobalTheory.HaarFundDom.setIntegral_eq_const_mul <;> assumption)
