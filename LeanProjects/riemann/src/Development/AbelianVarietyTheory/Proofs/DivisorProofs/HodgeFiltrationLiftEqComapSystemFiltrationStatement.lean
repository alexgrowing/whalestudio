import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftEqComapSystemFiltration
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCrystalHodgeLiftClasses_eq_comap_sys : CrystallineSmoothLift → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀], IsProper A₀.hom → GeometricallyConnected A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)), Smooth X.hom → ∀ S : Sys I π A₀.hom, S.Presents X.hom i → primitiveCrystalHodgeLiftClasses (divided₂ hI) A₀ X i h.w = (S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype := by
  first | exact @GlobalTheory.LiftSys.hodgeFiltration_lift_eq_comap_systemFiltration | exact GlobalTheory.LiftSys.hodgeFiltration_lift_eq_comap_systemFiltration | (intros; apply GlobalTheory.LiftSys.hodgeFiltration_lift_eq_comap_systemFiltration <;> assumption)
