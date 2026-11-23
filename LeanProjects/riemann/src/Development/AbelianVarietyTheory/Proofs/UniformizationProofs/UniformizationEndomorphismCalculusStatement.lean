import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.uniformizationEndomorphism_calculus : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ E E' E'' : EndU U.toUnifPre, (∀ g : GtPtF D.toPre F, ∃! g', E.Act g g') ∧ (∀ g₁ g₂ g₃ g₁' g₂' g₃' : GtPtF D.toPre F, g₁.IsAdd g₂ g₃ → E.Act g₁ g₁' → E.Act g₂ g₂' → E.Act g₃ g₃' → g₁'.IsAdd g₂' g₃') ∧ (∀ t (g g' : GtPtF D.toPre F), IsTor t g → E.Act g g' → IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) g') ∧ (E.aG = E'.aG → E.aB = E'.aB ∧ E.h = E'.h ∧ ∀ g g' : GtPtF D.toPre F, E.Act g g' ↔ E'.Act g g') ∧ (E''.aG = E.aG * E'.aG → E''.aB = E.aB * E'.aB ∧ E''.h = E.h + E'.h ∧ ∀ g g₁ g₂ g₃ : GtPtF D.toPre F, E.Act g g₁ → E'.Act g g₂ → g₁.IsAdd g₂ g₃ → E''.Act g g₃) ∧ (E''.aG = E.aG ≫ E'.aG → E''.aB = E.aB ≫ E'.aB ∧ E''.h = E.h.comp E'.h ∧ ∀ g g₁ g₂ : GtPtF D.toPre F, E.Act g g₁ → E'.Act g₁ g₂ → E''.Act g g₂) := by
  first | exact @GlobalTheory.EndCalc.end_calculus | exact GlobalTheory.EndCalc.end_calculus | (intros; apply GlobalTheory.EndCalc.end_calculus <;> assumption)
