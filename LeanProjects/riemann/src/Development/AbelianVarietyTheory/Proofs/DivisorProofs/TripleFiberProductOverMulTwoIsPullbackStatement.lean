import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleFiberProductOverMulTwoIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tripleFiberProductOverMulTwo_isPullback : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsPullback (t₁ A).left (ψ A).left A.hom (Two A ⊗ Two A).hom := by
  first | exact @GlobalTheory.TwoTors.TripleProd.isPullback | exact GlobalTheory.TwoTors.TripleProd.isPullback | (intros; apply GlobalTheory.TwoTors.TripleProd.isPullback <;> assumption)
