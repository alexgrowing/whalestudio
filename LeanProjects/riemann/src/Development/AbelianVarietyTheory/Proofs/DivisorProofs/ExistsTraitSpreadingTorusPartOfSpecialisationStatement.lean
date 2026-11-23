import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitSpreadingTorusPartOfSpecialisation
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
theorem _root_.GlobalTheory.T.exists_trait_spreading_torusPart_of_specialisation : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (G : Over Y) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ w w' : Y, w ⤳ w' → w ≠ w' → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ξ : Sp V ⟶ Y) (G₁ : Over (Sp V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left) (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Free ℤ X₁) (_ : Module.Finite ℤ X₁) (j : splitTorus (Sp V) X₁ ⟶ G₁) (GK : Over (Sp (FractionRing V))) (_ : GrpObj GK) (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), ξ (closedPoint V) = w' ∧ (spMap (algebraMap V (FractionRing V)) ≫ ξ) (closedPoint (FractionRing V)) = w ∧ IsGrpPullback G₁ G ξ φ₁ ∧ IsMonHom j ∧ IsTorPart (pullTorus hψ j) := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_trait_torusPart | exact GlobalTheory.Poinc.FibLat.exists_trait_torusPart | (intros; apply GlobalTheory.Poinc.FibLat.exists_trait_torusPart <;> assumption)
