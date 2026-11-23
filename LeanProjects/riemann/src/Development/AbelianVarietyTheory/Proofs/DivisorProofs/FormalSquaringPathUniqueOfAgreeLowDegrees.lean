import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomPowerSeriesEqOfRescale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeSquaringCotangentEqTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeUnitStalkDataStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_spMap_fromSpecStalk {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint (CommRingCat.of A)) = x) :
    ∃ g0 : X.presheaf.stalk x →+* A, spMap g0 ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨(Scheme.stalkClosedPointTo f).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem ringHom_eq_of_fromSpecStalk {X : Scheme.{0}} (x : X) {B : Type} [CommRing B]
    (f f' : X.presheaf.stalk x →+* B) (h : spMap f ≫ X.fromSpecStalk x = spMap f' ≫ X.fromSpecStalk x) : f = f' := by
  have h' : spMap f = spMap f' := (cancel_mono (X.fromSpecStalk x)).mp h
  have := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom this

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_constantCoeff_closedPoint (R : Type) [CommRing R] [IsLocalRing R] : (spMap (PowerSeries.constantCoeff (R := R))) (IsLocalRing.closedPoint (CommRingCat.of R)) = IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R)) := by
  haveI : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (PowerSeries.constantCoeff (R := R)))) :=
    ⟨fun _ h => PowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  exact Spec_closedPoint

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem path_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R) (n : ℕ), 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ ξ' : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G c b ξ' → (∀ (U : G.left.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(G.left, U)) (j : ℕ), 0 < j → j < n → PowerSeries.coeff j (evAt ξ h f) = PowerSeries.coeff j (evAt ξ' h' f)) → ξ = ξ' := by
  intro S G _ R _ _ hqs c n hn hc b ξ ξ' hξ hξ' hlow
  set s : S := b (IsLocalRing.closedPoint (CommRingCat.of R)) with hs
  set x : G.left := unitSec G s with hx
  have hpt : ∀ q0 : Sp (PowerSeries R) ⟶ G.left, IsPath G c b q0 →
      q0 (IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R))) = x := by
    intro q0 hq0
    have e := congrArg (fun q : Sp R ⟶ G.left => q (IsLocalRing.closedPoint (CommRingCat.of R))) hq0.zero
    change q0 (spMap PowerSeries.constantCoeff (IsLocalRing.closedPoint (CommRingCat.of R))) = unitSec G s at e
    rw [spMap_constantCoeff_closedPoint] at e
    exact e
  obtain ⟨π, ε, m, hSD, h1, h2, h3⟩ := GlobalTheory.T.exists_groupSchemeUnitStalkData S G s
  have hm := GlobalTheory.T.groupSchemeSquaring_cotangent_eq_two S G hqs s π ε m hSD
  obtain ⟨β, hβ⟩ := exists_spMap_fromSpecStalk b s rfl
  obtain ⟨g, hg⟩ := exists_spMap_fromSpecStalk ξ x (hpt ξ hξ)
  obtain ⟨g', hg'⟩ := exists_spMap_fromSpecStalk ξ' x (hpt ξ' hξ')
  have E1 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      k.comp π = PowerSeries.C.comp β := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk s
    rw [spMap_comp' π k, spMap_comp' β PowerSeries.C, Category.assoc, Category.assoc, hβ, hSD.str, ← Category.assoc, hk.base]
  have E2 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      PowerSeries.constantCoeff.comp k = β.comp ε := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k PowerSeries.constantCoeff, spMap_comp' ε β, Category.assoc, Category.assoc, hSD.unit, ← Category.assoc (spMap β), hβ, hk.zero]
  have E3 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      (PowerSeries.rescale c).comp k = k.comp m := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k (PowerSeries.rescale c), spMap_comp' m k, Category.assoc, Category.assoc, hSD.sq, hk.scale, Category.assoc]
  subst hg hg'
  have hlow' : ∀ j < n, ∀ f, PowerSeries.coeff j (g f) = PowerSeries.coeff j (g' f) := by
    intro j hj f
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have a := RingHom.congr_fun (E2 g hξ) f
      have a' := RingHom.congr_fun (E2 g' hξ') f
      simp only [RingHom.comp_apply] at a a'
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, a, a']
    · obtain ⟨U, hxU, f0, rfl⟩ := TopCat.Presheaf.germ_exist _ f
      obtain ⟨hh, hev⟩ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.2.2.2.2 (PowerSeries R) G.left x g U hxU
      obtain ⟨hh', hev'⟩ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.2.2.2.2 (PowerSeries R) G.left x g' U hxU
      have := hlow U hh hh' f0 j hj0 hj
      rw [hev, hev'] at this
      exact this
  have := ringHom_powerSeries_eq_of_rescale _ _ R π ε m β c n h1 h2 h3 hm hn hc g g' (E1 g hξ) (E1 g' hξ')
    (E2 g hξ) (E2 g' hξ') (E3 g hξ) (E3 g' hξ') hlow'
  rw [this]

end GlobalTheory.Nef
