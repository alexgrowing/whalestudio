import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackPolarizedLevelTriple_of_subring_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  first | exact @GlobalTheory.SiegBaseChange.pullbackTriple_of_le | exact GlobalTheory.SiegBaseChange.pullbackTriple_of_le | (intros; apply GlobalTheory.SiegBaseChange.pullbackTriple_of_le <;> assumption)
