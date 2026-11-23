import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeAboveValuationEq
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
theorem _root_.GlobalTheory.T.exists_prime_above_valuation_eq : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (𝔣 : Ideal (OF E)) (l : ℕ), l.Prime →
    ∃ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal ∧ ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P : ℚ) : ℝ) = c_vp 𝔣 l := by
  first | exact @GlobalTheory.CNumAtPrime.cNum_eq_c_vp | exact GlobalTheory.CNumAtPrime.cNum_eq_c_vp | (intros; apply GlobalTheory.CNumAtPrime.cNum_eq_c_vp <;> assumption)
