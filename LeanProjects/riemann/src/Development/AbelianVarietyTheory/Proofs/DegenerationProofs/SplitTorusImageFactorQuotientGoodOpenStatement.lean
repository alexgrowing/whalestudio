import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusImageFactorQuotientGoodOpen
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
theorem _root_.GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∃ (X' : Type) (_ : AddCommGroup X') (_ : Module.Free ℤ X') (_ : Module.Finite ℤ X') (i' : splitTorus (Sp k) X' ⟶ G) (ρ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X'), IsMonHom i' ∧ IsMonHom ρ ∧ Surjective ρ.left ∧ ρ ≫ i' = i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i' V) := by
  first | exact @GlobalTheory.TorusImage.exists_factor_goodOpen | exact GlobalTheory.TorusImage.exists_factor_goodOpen | (intros; apply GlobalTheory.TorusImage.exists_factor_goodOpen <;> assumption)
