import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.EtCover

variable {K : Type} [Field K]

def obj (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) : Over (Sp K) := Over.mk (π ≫ A.X.hom)

def hom (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) : obj A π ⟶ A.X := Over.homMk π rfl

@[simp] theorem obj_left (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) : (obj A π).left = Y := rfl

@[simp] theorem obj_hom (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) :
    (obj A π).hom = π ≫ A.X.hom := rfl

@[simp] theorem hom_left (A : AbVar K) {Y : Scheme.{0}} (π : Y ⟶ A.X.left) : (hom A π).left = π := rfl

end GlobalTheory.AV.EtCover
