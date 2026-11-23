import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
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
theorem _root_.GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) → ∃ (B : Over (Sp k)) (_ : GrpObj B) (q : G ⟶ B), IsQuot i q ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  first | exact @GlobalTheory.TorusQuotientGlue.main | exact GlobalTheory.TorusQuotientGlue.main | (intros; apply GlobalTheory.TorusQuotientGlue.main <;> assumption)
