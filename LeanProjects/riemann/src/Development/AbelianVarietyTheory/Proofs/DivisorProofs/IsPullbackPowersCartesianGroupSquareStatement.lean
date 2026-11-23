import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_powers_cartesian_group_square : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), IsPullback (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left (G2 G').hom (G2 G).hom f ∧ IsPullback (cubeMapOf h).F3 (G3 G').hom (G3 G).hom f ∧ IsPullback (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left (G4 G').hom (G4 G).hom f := by
  first | exact @GlobalTheory.Mum.PowCart.isPullback_pow | exact GlobalTheory.Mum.PowCart.isPullback_pow | (intros; apply GlobalTheory.Mum.PowCart.isPullback_pow <;> assumption)
