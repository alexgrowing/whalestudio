import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModule
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M] (u : Module.End ℤ_[l] (Tate l M)) (E : ℕ), 0 < E → u ^ E = 1 → (∀ t, (u t).lev 2 = t.lev 2) → u = 1 := by
  first | exact @GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two | exact GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two | (intros; apply GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two <;> assumption)
