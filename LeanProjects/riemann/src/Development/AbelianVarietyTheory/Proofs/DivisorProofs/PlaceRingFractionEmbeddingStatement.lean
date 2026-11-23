import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbedding
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
theorem _root_.GlobalTheory.T.place_ring_fraction_embedding : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (R : Subring ℂ) [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∃ j : FractionRing R →+* ℂ, (∀ x : R, j (algebraMap R (FractionRing R) x) = x) ∧ CharZero R ∧
      (l : R) ∈ IsLocalRing.maximalIdeal R ∧ Nat.card (E →+* FractionRing R) = Module.finrank ℚ E ∧
      (∀ σ : E →+* ℂ, ∃ τ : E →+* FractionRing R, j.comp τ = σ) ∧
      ∀ (x : FractionRing R) (r : ℚ), ((-r : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l x → Sz l lam (r : ℝ) (j x) := by
  first | exact @GlobalTheory.PlaceRingFacts.place_ring_facts | exact GlobalTheory.PlaceRingFacts.place_ring_facts | (intros; apply GlobalTheory.PlaceRingFacts.place_ring_facts <;> assumption)
