import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyAutomorphismShiftsJacobianOrder
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
theorem _root_.GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ f : A ≅ A, ∃ c : ℤ, ∀ (M : Model R A) (n : ℤ), HasOrd M D π n → HasOrd (M.twist f) D π (n + c) := by
  first | exact @GlobalTheory.SS.OrdTwist.main | exact GlobalTheory.SS.OrdTwist.main | (intros; apply GlobalTheory.SS.OrdTwist.main <;> assumption)
