import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem uOrdEq_stalkHom_of_associated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → Irreducible (h T.ϖ) → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → ∀ (a : M.Z.presheaf.stalk x) (k : ℕ), Associated (g' (j a)) (h T.ϖ ^ k) → UOrdEq M T ξ (M.stalkHom x a) k := by
  intro E _ _ _ H Dw l Xo c o' Ω _ _ _ M x T ξ hx R _ j V' _ _ _ h g' hinj hirr hcomm a k ha
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  let v : M.Z.presheaf.stalk x ⟶ CommRingCat.of T.V :=
    M.Z.presheaf.stalkSpecializes hx ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of T.V) ξ
  have hv : Spec.map v ≫ M.Z.fromSpecStalk x = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e1 : Spec.map (CommRingCat.ofHom j ≫ CommRingCat.ofHom g') = Spec.map (v ≫ CommRingCat.ofHom h) := by
    rw [← cancel_mono (M.Z.fromSpecStalk x), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hv]
    exact hcomm
  have e2 : g' (j a) = h (v.hom a) := congrArg (fun φ => φ.hom a) (Spec.map_injective e1)
  have e3 : M.val (jK T.V ≫ ξ) (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (v.hom a) := by
    refine (RatModel.val_spMap_comp (algebraMap T.V (FractionRing T.V)) ξ hx (M.stalkEquiv x a)).trans ?_
    rw [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]
  rw [e2] at ha
  have h0 : v.hom a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at ha
    exact pow_ne_zero k hirr.ne_zero (associated_zero_iff_eq_zero _ |>.1 ha.symm)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 T.irr
  have h1 : Associated (h T.ϖ ^ n) (h T.ϖ ^ k) := by
    refine Associated.trans ?_ ha
    rw [hu, map_mul, map_pow]
    exact (associated_unit_mul_left _ _ (u.isUnit.map h)).symm
  have hn : n = k := le_antisymm ((pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h1.dvd)
    ((pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h1.symm.dvd)
  exact ⟨u, by rw [e3, hu, hn, mul_comm]⟩

end GlobalTheory.UPoinc
