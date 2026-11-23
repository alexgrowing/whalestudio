import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep : ∀ C : Core, C.Indep → C.Fib := by
  first | exact @GlobalTheory.ZJ.Core.fib_of_indep | exact GlobalTheory.ZJ.Core.fib_of_indep | (intros; apply GlobalTheory.ZJ.Core.fib_of_indep <;> assumption)
