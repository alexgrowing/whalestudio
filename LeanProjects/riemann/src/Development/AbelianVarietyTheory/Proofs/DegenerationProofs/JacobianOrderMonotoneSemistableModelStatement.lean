import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobianOrderMonotoneSemistableModel
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
theorem _root_.GlobalTheory.T.jacobian_order_monotone_semistableModel : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [IsIntegral A.left] (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ (M N : Model R A) (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D π n → (∃ y ∈ M.sp, DefAt M N (𝟙 A) y) → m ≤ n ∧ (m = n → GenIso M N (𝟙 A)) := by
  first | exact @GlobalTheory.SS.OrdMono.ord_mono | exact GlobalTheory.SS.OrdMono.ord_mono | (intros; apply GlobalTheory.SS.OrdMono.ord_mono <;> assumption)
