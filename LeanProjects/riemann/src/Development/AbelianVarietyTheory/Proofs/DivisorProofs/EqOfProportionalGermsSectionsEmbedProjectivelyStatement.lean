import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectively
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N), GlobalTheory.AmpleSpan.EmbedsBy π s → ∀ (f₁ f₂ : X ⟶ Y), f₁ ≫ π = f₂ ≫ π → (∀ x : X, ∃ σ : κ → X.presheaf.stalk x, (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧ (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) → f₁ = f₂ := by
  first | (exact @GlobalTheory.HomFixGerm.eq_of_germs) | (exact GlobalTheory.HomFixGerm.eq_of_germs) | (intros; apply GlobalTheory.HomFixGerm.eq_of_germs  <;> assumption)
