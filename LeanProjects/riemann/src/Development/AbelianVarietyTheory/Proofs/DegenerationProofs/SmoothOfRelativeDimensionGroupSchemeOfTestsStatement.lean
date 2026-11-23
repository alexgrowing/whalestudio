import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTests
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests : ∀ C : Core, C.HasTests → C.Fib → SmoothOfRelativeDimension C.g C.GG.hom := by
  first | exact @GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests | exact GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests | (intros; apply GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests <;> assumption)
