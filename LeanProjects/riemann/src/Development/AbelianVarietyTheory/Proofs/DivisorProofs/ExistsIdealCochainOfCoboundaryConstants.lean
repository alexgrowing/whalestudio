import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem LiftSys.cobound_I : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S : Sys I π s₀) (z : Z1 S.F), S.IsIdealValuedLiftSystemCocycle z → H1.mk _ z = 0 → ∃ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g ∧ d0 _ g = z.1 := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hc S z hz h0
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h0
  obtain ⟨r₀, hr₀⟩ := hc (fun U ↦ S.p U (g U)) (by
    funext U V a
    have e := congrFun (congrFun (congrFun hg U) V) a
    rw [amitsur_d0_apply] at e
    rw [amitsur_d0_apply, ← S.nat a, ← map_sub, e]
    exact (S.ker V _).2 (hz U V a))
  obtain ⟨r, rfl⟩ := hπ r₀
  refine ⟨fun U ↦ g U - algebraMap R (S.F.obj U) r, fun U ↦ (S.ker U _).1 ?_, ?_⟩
  · rw [map_sub, hr₀ U, (S.semi U).map_algebraMap, sub_self]
  · rw [← hg]
    funext U V a
    simp only [amitsur_d0_apply, map_sub, AlgHom.commutes]
    ring

end GlobalTheory
