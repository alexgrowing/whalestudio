import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormOverDvrPrimeToL
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
theorem _root_.GlobalTheory.T.polarization_form_over_dvr_prime_to_l : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
    (∀ n : ℕ, n.Coprime l → IsUnit (n : R)) → ∀ (X : Obj F 𝔠 (Sp R)) (c₀ : 𝔠.elt), (c₀ : F) ≠ 0 →
    (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀) →
    ∀ ψ : LinearMap.BilinForm R (HdR X.A), GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c₀) ψ → Function.Bijective ψ := by
  first | exact @GlobalTheory.PolPrimeTo.perfect_of_primeTo | exact GlobalTheory.PolPrimeTo.perfect_of_primeTo | (intros; apply GlobalTheory.PolPrimeTo.perfect_of_primeTo <;> assumption)
