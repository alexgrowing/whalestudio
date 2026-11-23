import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
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
theorem _root_.GlobalTheory.T.exists_positiveDefinite_quadraticForm_endomorphisms : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∃ Q : (B ⟶ B) → ℤ, (∀ f g, Q (f * g) + Q (f * g⁻¹) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ (∀ f, IsMonHom f → Q f = 0 → f = 1) ∧ ∀ (F : B ⟶ B) (q : ℤ), PullPow F.left L q → ∀ f, Q (f ≫ F) = q * Q f := by
  first | exact @GlobalTheory.SS.exists_quadraticForm_end | exact GlobalTheory.SS.exists_quadraticForm_end | (intros; apply GlobalTheory.SS.exists_quadraticForm_end <;> assumption)
