import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackSemiAbelianDvr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_pullback_semiAbelian_dvr : ∀ (Y : Scheme.{0}) (G : Over Y) [GrpObj G], IsSemiAbelian G → ∀ (V : Type) [CommRing V] [IsDomain V] (Gu : Over (Sp V)) [GrpObj Gu], IsSemiAbelian Gu → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (fV : V →+* V') (ξ : Sp V' ⟶ Y) (AK : Over (Sp (FractionRing V'))) [GrpObj AK] (α : AK.left ⟶ Gu.left) (Ψ : AK.left ⟶ G.left), IsGrpPullback AK Gu (spMap ((algebraMap V' (FractionRing V')).comp fV)) α → IsGrpPullback AK G (spMap (algebraMap V' (FractionRing V')) ≫ ξ) Ψ → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left) (ω : AK.left ⟶ G'.left), IsGrpPullback G' Gu (spMap fV) β ∧ IsGrpPullback G' G ξ β' ∧ ω ≫ G'.hom = AK.hom ≫ spMap (algebraMap V' (FractionRing V')) ∧ ω ≫ β = α ∧ ω ≫ β' = Ψ ∧ ∀ (F : Gu ⟶ Gu) (f : G ⟶ G) (eK : AK ⟶ AK), eK.left ≫ α = α ≫ F.left → eK.left ≫ Ψ = Ψ ≫ f.left → ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ F.left ∧ F'.left ≫ β' = β' ≫ f.left := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr | exact GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr | (intros; apply GlobalTheory.Poinc.FibLat.exists_common_pullback_dvr <;> assumption)
