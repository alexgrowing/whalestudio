import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PureType
open scoped CategoryTheory.Obj

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
private theorem weil_pairing_properties : _root_.ReciprocityTheory.ChartRestriction.G.Out.WeilSt :=
  (_root_.GlobalTheory.AbLaw.FromCube.all_of_cubeGen
    (fun S P M a ↦ _root_.GlobalTheory.AbLaw.CubeAssembly.cube_gen S P M a)).2.2.2.2.1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.cmPoint_closed : _root_.GlobalTheory.CMPoint :=
  _root_.GlobalTheory.cmPoint _root_.GlobalTheory.thetaUnifAV_all weil_pairing_properties

end GlobalTheory
