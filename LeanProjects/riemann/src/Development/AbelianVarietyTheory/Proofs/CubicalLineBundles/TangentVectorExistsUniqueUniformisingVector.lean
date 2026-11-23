import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem existsUnique_isDiff_and_linear : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g), (∀ w, IsTangent w → ∃! W, u.IsDiff W w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR ℂ ⟶ x.P.A)) (W : Fin n → Fin x.P.g → ℂ) (cf : Fin n → ℂ) (w : epsR ℂ ⟶ x.P.A), (∀ i, IsTangent (v i)) → (∀ i, u.IsDiff (W i) (v i)) → IsLieComb cf v w → u.IsDiff (∑ i, cf i • W i) w :=
  fun x u => ⟨(GlobalTheory.AnyUnif.tangent_and_unimodular GlobalTheory.thetaUnifAV_all x.P u).1,
    fun n v W cf w => GlobalTheory.isDiff_sum_smul_of_isLieComb x.P.A x.P.isAb x.P.L x.P.g n u v W cf w⟩

end GlobalTheory.LamT
