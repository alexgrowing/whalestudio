import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianIsAbelianSchemeLocalizationAbelianLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_isAbelianScheme_localization_abelianLocus : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) := by
  first | exact @GlobalTheory.AbLocusAtPrime.isAbelianScheme_localization | exact GlobalTheory.AbLocusAtPrime.isAbelianScheme_localization | (intros; apply GlobalTheory.AbLocusAtPrime.isAbelianScheme_localization <;> assumption)
