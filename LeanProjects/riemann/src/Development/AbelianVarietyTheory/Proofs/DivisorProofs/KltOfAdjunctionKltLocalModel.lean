import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveVarietyOfIsLocalRingOfVarietyPoiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceEquivOfRingEquivOverConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrdQEqOrdDivOfRationalCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InversionOfAdjunctionProjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

section Transport

variable {k K K' : Type} [Field k] [Field K] [Field K'] {c : k →+* K} {c' : k →+* K'}

theorem Place.contains_map_iff (e : K ≃+* K') (E : Place c) (E' : Place c')
    (hring : ∀ a, e a ∈ E'.ring ↔ a ∈ E.ring) (R : Subring K) :
    E'.Contains (R.map e.toRingHom) ↔ E.Contains R := by
  constructor
  · intro h f hf
    exact (hring f).1 (h _ ⟨f, hf, rfl⟩)
  · rintro h _ ⟨f, hf, rfl⟩
    exact (hring f).2 (h f hf)

theorem Place.isPrimeOf_map_iff (e : K ≃+* K') (E : Place c) (E' : Place c')
    (hring : ∀ a, e a ∈ E'.ring ↔ a ∈ E.ring) (hord : ∀ a, E'.ord (e a) = E.ord a)
    (R : Subring K) : E'.IsPrimeOf (R.map e.toRingHom) ↔ E.IsPrimeOf R := by
  rw [Place.IsPrimeOf, Place.IsPrimeOf, Place.contains_map_iff e E E' hring]
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f' hf' => ?_⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hb0, hbo, hfb⟩ := h (e f) ((hring f).2 hf)
    refine ⟨a, ha, b, hb, fun h0 => hb0 (by simp [h0]), (hord b).symm.trans hbo, e.injective ?_⟩
    simpa using hfb
  · obtain ⟨a, ha, b, hb, hb0, hbo, hfb⟩ := h (e.symm f') ((hring _).1 (by simpa using hf'))
    refine ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, by simpa using hb0, (hord b).trans hbo, ?_⟩
    rw [← hfb]
    simp

theorem adjKlt_congr {n : ℕ} {T : Subring K} {S : Place c} {η : Forms c n} {φ ψ : K →₀ ℚ}
    (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (h : ∀ P : Place c, P.ordQ φ = P.ordQ ψ) : AdjKlt c n T S η φ ↔ AdjKlt c n T S η ψ := by
  have h' : ∀ P : Place c, P.disc η φ = P.disc η ψ := fun P => by rw [Place.disc, Place.disc, h]
  simp only [AdjKlt, h', hφ, hψ]

end Transport

theorem klt_of_adjKlt_locModel : GlobalTheory.Published.Principalisation → ∀ {L : Type} [Field L] (c : ℂ →+* L)
    (n : ℕ) (T : Subring L) (x : Fin n → L) (φ : L →₀ ℚ) (f : L) (S : Place c), IsLocModel c T →
    IsIntegrallyClosed T → TrBasis c x → f ∈ T → f ≠ 0 → S.IsPrimeOf T → S.ord f = 1 →
    S.disc (dForm c x) φ = 0 → EffAt c n T (dForm c x) φ →
    AdjKlt c n T S (dForm c x) (φ + Finsupp.single f 1) → Klt c n T (dForm c x) φ := by
  intro hP L _ c n T x φ f S hT hTic hx hfT hf0 hS hSf hSd hEff hAdj
  obtain ⟨Y, hY, p, e, y, hproj, hdim, hc, hy⟩ := GlobalTheory.T.exists_projectiveVariety_of_isLocalRingOfVarietyPoint L c T n x hT hx
  haveI := hY
  haveI : LocallyOfFiniteType p := GlobalTheory.isProjOver_locallyOfFiniteType ℂ Y p hproj
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have hc' : ∀ a, e.symm (c a) = Cartier.constFn p a := fun a => by
    rw [← hc a]
    exact e.symm_apply_apply _
  have hyT : T.map e.symm.toRingHom = locRing y := by
    rw [← hy]
    ext z
    simp [Subring.mem_map]
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_dvrPlace_equiv_of_ringEquiv_over_constants c (Cartier.constFn p) e.symm hc'
  obtain ⟨hx', -, -, -⟩ := GlobalTheory.T.ringEquiv_transports_varietyPair_data c (Cartier.constFn p) e.symm hc' n x T φ hx
  have hψ0 : (φ + Finsupp.single f 1 : L →₀ ℚ) 0 = 0 := by
    simp [hEff.apply_zero, Finsupp.single_apply, hf0]
  obtain ⟨m, g, hm, hg⟩ := GlobalTheory.T.exists_ordQ_eq_ord_div_of_rational_combination (Cartier.constFn p)
    (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) (by
      rw [← map_zero e.symm, Finsupp.mapDomain_apply e.symm.injective]
      exact hψ0)

  have hkey : ∀ E : Place c, (Φ E).disc (dForm (Cartier.constFn p) (e.symm ∘ x))
      (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) =
      E.disc (dForm c x) (φ + Finsupp.single f 1) := fun E => by
    rw [Place.disc, Place.disc, (hΦ E).2.2.1, (hΦ E).2.2.2 n x hx]
  have hψ : ∀ E : Place c, E.disc (dForm c x) (φ + Finsupp.single f 1) =
      E.disc (dForm c x) φ - E.ord f := fun E => by
    simp only [Place.disc, map_add, Place.ordQ_single]
    ring
  have hordQ : ∀ P : Place (Cartier.constFn p),
      P.ordQ (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) =
      P.ordQ (Finsupp.single (g : Y.functionField) (1 / (m : ℚ))) := fun P => by
    rw [hg, Place.ordQ_single]
    ring
  have hdisc : ∀ D : DivOver p, discrep D (dForm (Cartier.constFn p) (e.symm ∘ x)) m g =
      (Φ.symm (placeEquiv p D)).disc (dForm c x) (φ + Finsupp.single f 1) := fun D => by
    rw [← disc_placeEquiv, ← hkey, Φ.apply_symm_apply, Place.disc, Place.disc, hordQ]
  let f' : Y.functionFieldˣ := Units.mk0 (e.symm f) (by simpa using hf0)
  have hord : ∀ D : DivOver p, (D.ord f' : ℚ) = (Φ.symm (placeEquiv p D)).ord f := fun D => by
    rw [← ord_placeEquiv]
    have h := (hΦ (Φ.symm (placeEquiv p D))).2.1 f
    rw [Φ.apply_symm_apply] at h
    exact_mod_cast h

  have hstalk : IsIntegrallyClosed (Y.presheaf.stalk y) := by
    let e₁ : Y.presheaf.stalk y ≃+* locRing y := RingEquiv.ofBijective
      (algebraMap (Y.presheaf.stalk y) Y.functionField).rangeRestrict
      ⟨fun _ _ h => IsFractionRing.injective _ Y.functionField (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
    have : IsIntegrallyClosed (locRing y) := IsIntegrallyClosed.of_equiv
      ((T.equivMapOfInjective e.symm.toRingHom e.symm.injective).trans
        (RingEquiv.subringCongr hyT))
    exact IsIntegrallyClosed.of_equiv e₁.symm
  have hreg : RegAt y (f' : Y.functionField) := by
    rw [← mem_locRing, ← hyT]
    exact ⟨f, hfT, rfl⟩
  have hSprime : (placeEquiv p ((placeEquiv p).symm (Φ S))).IsPrimeOf (locRing y) := by
    rw [Equiv.apply_symm_apply, ← hyT]
    exact (Place.isPrimeOf_map_iff e.symm S (Φ S) (hΦ S).1 (hΦ S).2.1 T).2 hS
  have hSord : ((placeEquiv p).symm (Φ S)).ord f' = 1 := by
    have h := hord ((placeEquiv p).symm (Φ S))
    rw [Equiv.apply_symm_apply, Φ.symm_apply_apply, hSf] at h
    exact_mod_cast h
  have hSdisc : discrep ((placeEquiv p).symm (Φ S)) (dForm (Cartier.constFn p) (e.symm ∘ x)) m g
      = -1 := by
    rw [hdisc, Equiv.apply_symm_apply, Φ.symm_apply_apply, hψ, hSd, hSf]
    norm_num
  have heff : ∀ D : DivOver p, (placeEquiv p D).IsPrimeOf (locRing y) →
      discrep D (dForm (Cartier.constFn p) (e.symm ∘ x)) m g ≤ 0 := by
    intro D hD
    have hE : (Φ.symm (placeEquiv p D)).IsPrimeOf T := by
      refine (Place.isPrimeOf_map_iff e.symm _ (Φ (Φ.symm (placeEquiv p D)))
        (hΦ _).1 (hΦ _).2.1 T).1 ?_
      rw [Φ.apply_symm_apply, hyT]
      exact hD
    have h0 : (0 : ℚ) ≤ (Φ.symm (placeEquiv p D)).ord f := by
      exact_mod_cast ((Φ.symm (placeEquiv p D)).ord_nonneg_iff hf0).2 (hE.1 f hfT)
    rw [hdisc, hψ]
    linarith [hEff.disc_le hE]
  have hadj : AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p ((placeEquiv p).symm (Φ S)))
      (dForm (Cartier.constFn p) (e.symm ∘ x)) (Finsupp.single (g : Y.functionField) (1 / (m : ℚ))) := by
    rw [Equiv.apply_symm_apply, ← hyT]
    have h := GlobalTheory.T.kltAlongPlaceNeighbours_ringEquiv c (Cartier.constFn p) e.symm hc' n x T _ S (Φ S) hx (hΦ S).1 hAdj
    exact (adjKlt_congr h.apply_zero (Finsupp.single_eq_of_ne g.ne_zero.symm) hordQ).1 h
  have hmain := GlobalTheory.T.inversion_of_adjunction_proj_alt hP Y p n hproj hdim (e.symm ∘ x) m g f' y ((placeEquiv p).symm (Φ S))
    hx' hm hstalk hreg hSprime hSord hSdisc heff hadj
  refine ⟨hEff.form_ne_zero, hEff.apply_zero, fun E hE => ?_⟩
  have hThr : ((placeEquiv p).symm (Φ E)).Through y := by
    rw [← contains_placeEquiv, Equiv.apply_symm_apply, ← hyT]
    exact (Place.contains_map_iff e.symm E (Φ E) (hΦ E).1 T).2 hE
  have h := hmain _ hThr
  rw [hdisc, hord, Equiv.apply_symm_apply, Φ.symm_apply_apply, hψ] at h
  linarith

end GlobalTheory.FieldPair
