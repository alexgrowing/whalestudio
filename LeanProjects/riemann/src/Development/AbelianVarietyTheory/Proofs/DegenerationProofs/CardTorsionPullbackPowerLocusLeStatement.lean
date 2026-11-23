import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionPullbackPowerLocusLe
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
theorem _root_.GlobalTheory.T.card_torsion_pullbackPowerLocus_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G →  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → IsAbelianScheme B → ∀ (L : LB G.left), AmpleCub G L → ∀ (F : G ⟶ G) (Q : ℕ), 2 ≤ Q → IsMonHom F → PullPow F.left L Q → i ≫ F = i ^ Q → ∃ C : ℕ, ∀ n, 1 ≤ n → Finite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ≫ F = x ^ Q ∧ x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ≫ F = x ^ Q ∧ x ^ n = 1} ≤ C * n ^ Module.finrank ℤ X := by
  first | exact @GlobalTheory.SS.PowLocus.card_torsion_powLocus_le | exact GlobalTheory.SS.PowLocus.card_torsion_powLocus_le | (intros; apply GlobalTheory.SS.PowLocus.card_torsion_powLocus_le <;> assumption)
