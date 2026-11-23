import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_lift_finite_cover_normal_local : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsIntegrallyClosed V₁ → ∀ (X Z : Scheme.{0}) (π : X ⟶ Z), IsFinite π → ∀ (f : Sp V₁ ⟶ Z) (yM : Sp (FractionRing V₁) ⟶ X), yM ≫ π = jK V₁ ≫ f → ∃ (z₁ : X) (ev : X.presheaf.stalk z₁ →+* V₁), IsLocalHom ev ∧ spMap ev ≫ X.fromSpecStalk z₁ ≫ π = f ∧ jK V₁ ≫ spMap ev ≫ X.fromSpecStalk z₁ = yM := by
  first | exact @GlobalTheory.FiniteLift.exists_stalk_lift | exact GlobalTheory.FiniteLift.exists_stalk_lift | (intros; apply GlobalTheory.FiniteLift.exists_stalk_lift <;> assumption)
