import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq : ∀ (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens), IsAffineOpen W → ∀ (g₀ g₁ : Sp (Polynomial K) ⟶ Y), (∀ x, g₀ x ∈ W) → (∀ x, g₁ x ∈ W) → spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) : Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁ → g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  first | exact @GlobalTheory.chart_map_into_affine_const | exact GlobalTheory.chart_map_into_affine_const | (intros; apply GlobalTheory.chart_map_into_affine_const <;> assumption)
