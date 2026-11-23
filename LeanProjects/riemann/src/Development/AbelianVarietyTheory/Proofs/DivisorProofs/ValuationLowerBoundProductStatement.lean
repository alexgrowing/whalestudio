import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLowerBoundProduct
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
theorem _root_.GlobalTheory.T.valuation_lower_bound_product : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ),
    (l : R) ∈ IsLocalRing.maximalIdeal R → (l : R) ≠ 0 →
    ∀ (a b δ : FractionRing R) (u : Rˣ) (ca cd : ℚ), a ≠ 0 → b ≠ 0 → δ ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l a ≤ (ca : WithTop ℚ) → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l b ≤ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l δ = (cd : WithTop ℚ) →
      ((-(ca + cd) : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l ((algebraMap R (FractionRing R) (u : R)) ^ 2 / (a * (δ * b))) := by
  first | exact @GlobalTheory.ValArith.val_sq_div_ge | exact GlobalTheory.ValArith.val_sq_div_ge | (intros; apply GlobalTheory.ValArith.val_sq_div_ge <;> assumption)
