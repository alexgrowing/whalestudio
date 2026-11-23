import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (U V : AffOp X₀), (∃ Q : S.thickObj hI U ⟶ (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop)), ∀ b, Q.φ b = S.p U b) ∧ ∀ (Q : S.thickObj hI U ⟶ (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop))), (∀ b, Q.φ b = S.p U b) → ∀ (α β : S.thickObj hI U ⟶ S'.thickObj hI V) (θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), IsTheta I (S.p U) α.φ β.φ θ → ∀ f : Z1 (O (divided₂ hI) (s₀ ≫ spMap π)), ev f β - ev f α = θ (connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) - D R₀ (Sec s₀ U.unop.1) (ev f Q : Sec s₀ U.unop.1)) := by
  first | exact @GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq | exact GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq | (intros; apply GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq <;> assumption)
