import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionTranslationActsOnExpansions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionTranslation_acts_on_expansions : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W) (N : ℕ), 1 ≤ N → ∀ (x : TA V W ⟶ G) (g' : GtPt D (TA V W)) (g : GtPtF D F) (xA : TFK (R := V) F ⟶ A.A), x ^ N = 1 → U.Red x g' → GtPt.IsPullF F φ.left g' g → U.SamePt xA (φ ≫ x) → U.Acts F N 0 g xA) := by
  first | exact @GlobalTheory.UU.Transl.main | exact GlobalTheory.UU.Transl.main | (intros; apply GlobalTheory.UU.Transl.main <;> assumption)
