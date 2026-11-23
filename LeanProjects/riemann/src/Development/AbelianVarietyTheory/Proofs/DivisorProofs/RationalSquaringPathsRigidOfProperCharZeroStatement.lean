import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfProperCharZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_proper_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (H : Over (Sp Ω)) [GrpObj H], IsProper H.hom → RatRigid H (𝟙 (Sp Ω)) := by
  first | exact @GlobalTheory.Nef.ratRigid_of_isProper_of_charZero | exact GlobalTheory.Nef.ratRigid_of_isProper_of_charZero | (intros; apply GlobalTheory.Nef.ratRigid_of_isProper_of_charZero <;> assumption)
