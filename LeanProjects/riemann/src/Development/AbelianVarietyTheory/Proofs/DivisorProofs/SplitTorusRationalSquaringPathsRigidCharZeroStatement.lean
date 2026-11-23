import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusRationalSquaringPathsRigidCharZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_rationalSquaringPathsRigid_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Type) [AddCommGroup X], RatRigid (splitTorus (Sp Ω) X) (𝟙 (Sp Ω)) := by
  first | exact @GlobalTheory.Nef.splitTorus_ratRigid | exact GlobalTheory.Nef.splitTorus_ratRigid | (intros; apply GlobalTheory.Nef.splitTorus_ratRigid <;> assumption)
