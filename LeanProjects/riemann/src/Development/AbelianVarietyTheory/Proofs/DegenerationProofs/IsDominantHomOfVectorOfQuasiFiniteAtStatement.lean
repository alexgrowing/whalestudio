import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsDominantHomOfVectorOfQuasiFiniteAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isDominant_homOfVector_of_quasiFiniteAt' : ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  first | exact @GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | exact GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt | (intros; apply GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt <;> assumption)
