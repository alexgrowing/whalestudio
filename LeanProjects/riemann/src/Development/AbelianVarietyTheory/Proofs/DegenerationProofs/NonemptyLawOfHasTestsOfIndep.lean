import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndepStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTestsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestCartOfSpecialFibreSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesianStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosureStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosureStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.nonempty_law_of_hasTests_of_indep :
    ∀ C : Core, C.HasTests → C.Indep → Nonempty C.Law := by
  intro C hT hI
  have hF : C.Fib := GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep C hI
  have hS := GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests C hT hF
  have hC : C.TestCart := GlobalTheory.T.testCart_of_specialFibre_surjective C hF hS
  have hL : C.FibLaw := GlobalTheory.T.fibreLaw_of_testCartesian C hC
  exact GlobalTheory.T.nonempty_law_abelianSchemeProperClosure C hS hC (GlobalTheory.T.exists_mul_of_isSquare_of_fibLaw C hT hS hC hL) (GlobalTheory.T.exists_inverse_extension_properClosure C hT hS hC hL)

end GlobalTheory.ZJ
