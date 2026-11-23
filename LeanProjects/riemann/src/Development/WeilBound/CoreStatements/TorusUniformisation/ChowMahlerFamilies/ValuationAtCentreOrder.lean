import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ValuationOrder

theorem specializes_comp {X : Scheme.{0}} {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S]
    (z : Spec R ⟶ X) (φ : R ⟶ S) :
    (Spec.map φ ≫ z) (IsLocalRing.closedPoint S) ⤳ z (IsLocalRing.closedPoint R) := by
  have h := (IsLocalRing.specializes_closedPoint
    ((Spec.map φ) (IsLocalRing.closedPoint S))).map z.continuous
  exact (Scheme.Hom.comp_apply (Spec.map φ) z (IsLocalRing.closedPoint S)).symm ▸ h

theorem stalk_comp {X : Scheme.{0}} {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S]
    (z : Spec R ⟶ X) (φ : R ⟶ S) :
    X.presheaf.stalkSpecializes (specializes_comp z φ) ≫ Scheme.stalkClosedPointTo (Spec.map φ ≫ z) =
      Scheme.stalkClosedPointTo z ≫ φ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (z (IsLocalRing.closedPoint R))), Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_spec {p q : X} (hp : genPt ξ ⤳ p) (hpq : p ⤳ q) (s : X.presheaf.stalk q) :
    genMap ξ ⟨p, hp⟩ ((X.presheaf.stalkSpecializes hpq).hom s) = genMap ξ ⟨q, hp.trans hpq⟩ s := by
  have h1 : X.presheaf.stalkSpecializes hpq ≫ X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ =
      X.presheaf.stalkSpecializes (hp.trans hpq) ≫ Scheme.stalkClosedPointTo ξ := by
    rw [← X.presheaf.stalkSpecializes_comp hp hpq]
    exact (Category.assoc _ _ _).symm
  have h2 := congrArg (fun f => CommRingCat.Hom.hom f s) h1
  rw [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

theorem valAt_comp {V C : Type} [CommRing V] [IsLocalRing V] [CommRing C] [IsLocalRing C]
    (φ : V →+* C) {z : Spec (CommRingCat.of V) ⟶ X}
    (h : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) {a : Ω} {r : V} (hv : ValAt ξ z a r) :
    ValAt ξ (Spec.map (CommRingCat.ofHom φ) ≫ z) a (φ r) := by
  obtain ⟨_, s, rfl, rfl⟩ := hv
  refine ⟨h, (X.presheaf.stalkSpecializes (specializes_comp z (CommRingCat.ofHom φ))).hom s,
    genMap_spec h _ s, ?_⟩
  exact congrArg (fun f => f.hom s) (stalk_comp z (CommRingCat.ofHom φ))

section

variable {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem valAt_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') :
    r = r' := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  obtain ⟨_, s', e, rfl⟩ := h'
  rw [hξ.inj ⟨centre z, hz⟩ e]

theorem valAt_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t * t', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_pow {a : Ω} {r : R} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  exact ⟨hz, t ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem ne_zero_of_valAt {a : Ω} {r : R} (h : ValAt ξ z a r) (hr : IsUnit r) : a ≠ 0 := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  have ht : IsUnit t := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit t hr
  exact (ht.map (genMap ξ ⟨centre z, hz⟩)).ne_zero

theorem exists_unit_val (hξ : IsCptGen ξ) {h : genPt ξ ⤳ centre z} {b : Ω} (hb : unitAt ξ ⟨centre z, h⟩ b) :
    ∃ u : Rˣ, ValAt ξ z b u := by
  obtain ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩ := hb
  have h1 : ValAt ξ z b _ := ⟨h, s, hs, rfl⟩
  have h2 : ValAt ξ z b⁻¹ _ := ⟨h, t, ht, rfl⟩
  have h3 := valAt_mul h1 h2
  rw [mul_inv_cancel₀ h0] at h3
  have h4 : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩
  exact ⟨Units.mkOfMulEqOne _ _ (valAt_unique hξ h3 h4), h1⟩

end

end PositivityTheory.Xgn.ValuationOrder

open PositivityTheory.Xgn.ValuationOrder in
theorem PositivityTheory.Xgn.valuation_at_centre_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u := by
  intro X Ω _ ξ L σ ϖ M a V C _ _ _ _ z h e γ π hξ hord hgen hγ hπ hπ0
  have hu : unitAt ξ ⟨centre z, h⟩ ((σ / e) ^ M / ϖ ^ a) := (orderAt_iff_div hgen.1 hgen.2).1 hord
  obtain ⟨u, hval⟩ := exists_unit_val hξ hu
  have hc := valAt_comp (algebraMap V C) hγ.1 hval
  have hϖ : ϖ ≠ 0 := ne_zero_of_valAt hπ hπ0.isUnit
  have hM := valAt_pow hγ M
  refine ⟨u, ?_⟩
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · have h1 := valAt_mul (valAt_pow hπ n) hc
    rw [zpow_natCast, mul_div_cancel₀ _ (pow_ne_zero n hϖ)] at h1
    rw [zpow_natCast]
    exact valAt_unique hξ hM h1
  · have h1 := valAt_mul hM (valAt_pow hπ n)
    rw [zpow_neg, zpow_natCast, div_inv_eq_mul] at hc
    rw [← valAt_unique hξ h1 hc, zpow_neg, zpow_natCast]
    field_simp
