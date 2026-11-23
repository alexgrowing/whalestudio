import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfTorusExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_torusExtension : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (G : Over (Sp Ω)) [GrpObj G], Nonempty (TorusExtension G) → RatRigid G (𝟙 (Sp Ω)) := by
  first | exact @GlobalTheory.Nef.ratRigid_of_torusExtension | exact GlobalTheory.Nef.ratRigid_of_torusExtension | (intros; apply GlobalTheory.Nef.ratRigid_of_torusExtension <;> assumption)
