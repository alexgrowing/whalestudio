import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cohomology_iso_presented_crystal : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (h : IsPullback i s₀ s (spMap π)), S.Presents s i → ∃ e : HO1 s ≃ₗ[R] GlobalTheory.CatCoh.H1 S.F, (∀ (m : IsMor (dp0 R) s (divided₂ hI) (s₀ ≫ spMap π) (RingHom.id R) i) (c : FirstDeRham s), e (toHO1 s (cmp1 s c)) = S.r hI (m.pull1 c)) ∧ ∀ c : HO1 s, IsPullO h.w c (S.redO.pull1 (e c)) := by
  first | exact @GlobalTheory.LiftSys.cohomology_presents | exact GlobalTheory.LiftSys.cohomology_presents | (intros; apply GlobalTheory.LiftSys.cohomology_presents <;> assumption)
