import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfIsogeny
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialSemiAbelianReduction_of_isogeny : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SS.potModel_semiAbelian_of_isogeny | exact GlobalTheory.SS.potModel_semiAbelian_of_isogeny | (intros; apply GlobalTheory.SS.potModel_semiAbelian_of_isogeny <;> assumption)
