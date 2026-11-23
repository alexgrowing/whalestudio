import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierEqOfPrimitiveAdjointBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMultiplier_eq_of_primitive_adjoint_bundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (f f' : G ⟶ G), IsMonHom f → IsMonHom f' → f * f' = 𝟙 G → AdjCls (cls U.LG.L U.LG.isLB) (cls U.LG.L U.LG.isLB) f f' → cls U.LG.L U.LG.isLB = lam (cls U.LG.L U.LG.isLB) (𝟙 G) f → ∀ (fB : D.toPre.P.A ⟶ D.toPre.P.A) (m : D.toPre.X → D.toPre.X), Over₀ U.toUnifPre U.toUnifPre f fB → OnTorus U.toUnifPre U.toUnifPre f' m → PrimVal D.toPre fB m := by
  first | exact @GlobalTheory.PrimAdj.primVal_of_adj | exact GlobalTheory.PrimAdj.primVal_of_adj | (intros; apply GlobalTheory.PrimAdj.primVal_of_adj <;> assumption)
