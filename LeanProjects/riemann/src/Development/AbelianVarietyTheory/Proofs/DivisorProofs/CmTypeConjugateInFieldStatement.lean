import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeConjugateInField
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_conjugate_in_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K] (j : K →+* ℂ) (I : Type)
    (φ : I → E →+* ℂ) (φK : I → E →+* K), (∀ i, j.comp (φK i) = φ i) → IsCMType φ →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  first | exact @GlobalTheory.CMTypeThroughField.isCMTypeIn_bar | exact GlobalTheory.CMTypeThroughField.isCMTypeIn_bar | (intros; apply GlobalTheory.CMTypeThroughField.isCMTypeIn_bar <;> assumption)
