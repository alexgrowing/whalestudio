import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifPullGuards

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in

theorem _root_.GlobalTheory.UnifPullGuards.unifBaseChange_holds : _root_.ReciprocityTheory.ChartRestriction.G.Out.UnifBaseChangeSt :=
  _root_.GlobalTheory.unifBaseChange _root_.GlobalTheory.polBaseChange_holds
    _root_.GlobalTheory.globalFns_holds _root_.GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    _root_.GlobalTheory.twistBaseChange

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

end GlobalTheory.UnifPullGuards
