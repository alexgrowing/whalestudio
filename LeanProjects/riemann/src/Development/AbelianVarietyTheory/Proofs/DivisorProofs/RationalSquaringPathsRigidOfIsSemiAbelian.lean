import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMapStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratRigid_of_isSemiAbelian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G →
    ∀ (F : Type) [Field F] [CharZero F] (b : Sp F ⟶ S), RatRigid G b := by
  intro S G _ hG F _ _ b
  let Ω := AlgebraicClosure F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hE : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap F Ω) ≫ b)).obj G)) :=
    hG.fibres Ω (spMap (algebraMap F Ω) ≫ b)
  have h1 := GlobalTheory.T.rationalSquaringPathsRigid_of_torusExtension Ω ((Over.pullback (spMap (algebraMap F Ω) ≫ b)).obj G) hE
  have h2 := GlobalTheory.T.rationalSquaringPathsRigid_of_fibre S G Ω (spMap (algebraMap F Ω) ≫ b) h1
  exact GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map S G F Ω (algebraMap F Ω) b h2

end GlobalTheory.Nef
