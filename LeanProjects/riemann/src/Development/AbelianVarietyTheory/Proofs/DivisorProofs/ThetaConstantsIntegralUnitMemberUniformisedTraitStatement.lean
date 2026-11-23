import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsIntegralUnitMemberUniformisedTrait
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constants_integral_unit_member_uniformised_trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G) (σ : SecAt G U.LG.L (𝟙 (Sp W))), NZ G U.LG.L (𝟙 (Sp W)) σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : W) → ∀ (K : Type) [Field K] [IsAlgClosed K] (i : W →+* K) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp W)) ⟶ G)) (c : Fin N → K), Function.Injective i → ThList G U.LG.L U.LG.rig m (spMap i ≫ 𝟙 (Sp W)) (SecAt.pull G U.LG.L σ i) pt c → Prim i c := by
  first | exact @GlobalTheory.UMin.PrimModel.main | exact GlobalTheory.UMin.PrimModel.main | (intros; apply GlobalTheory.UMin.PrimModel.main <;> assumption)
