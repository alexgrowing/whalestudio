import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSqrtNegPrime
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbeddingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_sqrt_neg_prime : ∀ (E : Type) [Field E] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R],
    (l : R) ∈ IsLocalRing.maximalIdeal R → (∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : R)) →
    ∀ (d : ℕ), d.Prime → ∀ (δ : E), δ ^ 2 = -(d : E) → ∀ σ : E →+* FractionRing R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ δ) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
  first | exact @GlobalTheory.val_vp_sqrt_neg_prime | exact GlobalTheory.val_vp_sqrt_neg_prime | (intros; apply GlobalTheory.val_vp_sqrt_neg_prime <;> assumption)
