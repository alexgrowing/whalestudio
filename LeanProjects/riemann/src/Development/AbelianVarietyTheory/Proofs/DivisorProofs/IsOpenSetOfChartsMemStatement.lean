import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSetOfChartsMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_setOf_fibre_charts_mem : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (g₀ g₁ : Sp (Polynomial R) ⟶ Y), spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ g₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ g₁ → ∀ (W : Y.Opens), IsOpen {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W} := by
  first | exact @GlobalTheory.isOpen_setOf_charts_mem | exact GlobalTheory.isOpen_setOf_charts_mem | (intros; apply GlobalTheory.isOpen_setOf_charts_mem <;> assumption)
