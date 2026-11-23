import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.RingEquivTransport

section General

variable {k A B : Type} [CommRing k] [CommRing A] [CommRing B]

theorem isFreeGen_map {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    {σ : A →+* B} (hσ : Function.Bijective σ) (F : M →ₛₗ[σ] N) (hF : Function.Bijective F)
    {ω : M} (h : IsFreeGen A ω) : IsFreeGen B (F ω) := by
  refine ⟨fun b b' hb => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := hσ.2 b
    obtain ⟨a', rfl⟩ := hσ.2 b'
    have : F (a • ω) = F (a' • ω) := by
      rw [F.map_smulₛₗ, F.map_smulₛₗ]
      exact hb
    exact congrArg σ (h.1 (hF.1 this))
  · obtain ⟨x, rfl⟩ := hF.2 y
    obtain ⟨a, rfl⟩ := h.2 x
    exact ⟨σ a, (F.map_smulₛₗ a ω).symm⟩

theorem formMap_symm_formMap {α : k →+* A} {β : k →+* B} (ρ : A ≃+* B)
    (h : ρ.toRingHom.comp α = β) (h' : ρ.symm.toRingHom.comp β = α) (D : ℕ) (x : Forms α D) :
    TopForm.formMap D ρ.symm.toRingHom h' (TopForm.formMap D ρ.toRingHom h x) = x :=
  (TopForm.formMap_formMap _ _ (RingHom.id A) (RingHom.ext fun a => by simp) h h'
    (RingHom.id_comp α) x).trans (TopForm.formMap_of_eq_id _ rfl _ x)

theorem formMap_bijective {α : k →+* A} {β : k →+* B} (ρ : A ≃+* B)
    (h : ρ.toRingHom.comp α = β) (D : ℕ) :
    Function.Bijective (TopForm.formMap D ρ.toRingHom h) := by
  have h' : ρ.symm.toRingHom.comp β = α := by
    rw [← h]
    exact RingHom.ext fun a => by simp
  have h'' : ρ.symm.symm.toRingHom.comp α = β := h
  exact ⟨Function.LeftInverse.injective (formMap_symm_formMap ρ h h' D),
    Function.RightInverse.surjective (formMap_symm_formMap ρ.symm h' h'' D)⟩

end General

variable {k K K' : Type} [Field k] [Field K] [Field K']
variable {c : k →+* K} {c' : k →+* K'} (e : K ≃+* K') (he : ∀ a, e (c a) = c' a)

def ringEquiv (E : ValuationSubring K) : E ≃+* E.comap e.symm.toRingHom where
  toFun x := ⟨e x.1, ValuationSubring.mem_comap.2 (by simp)⟩
  invFun y := ⟨e.symm y.1, ValuationSubring.mem_comap.1 y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)

theorem ringEquiv_apply (E : ValuationSubring K) (x : E) : ((ringEquiv e E x : E.comap e.symm.toRingHom) : K') = e x :=
  rfl

def place (E : Place c) : Place c' where
  ring := E.ring.comap e.symm.toRingHom
  const_mem a := ValuationSubring.mem_comap.2 (by
    change e.symm (c' a) ∈ E.ring
    rw [← he a, e.symm_apply_apply]
    exact E.const_mem a)
  dvr := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (ringEquiv e E.ring)
  essFiniteType := by
    have h := E.essFiniteType.comp (RingHom.FiniteType.of_surjective
      (ringEquiv e E.ring).toRingHom (ringEquiv e E.ring).surjective).essFiniteType
    convert h using 1
    exact RingHom.ext fun a => Subtype.ext (he a).symm

theorem mem_place (E : Place c) (y : K') : y ∈ (place e he E).ring ↔ e.symm y ∈ E.ring :=
  ValuationSubring.mem_comap

theorem apply_mem_place (E : Place c) (f : K) : e f ∈ (place e he E).ring ↔ f ∈ E.ring := by
  rw [mem_place, e.symm_apply_apply]

theorem symm_apply (he : ∀ a, e (c a) = c' a) (a : k) : e.symm (c' a) = c a := by
  rw [← he a, e.symm_apply_apply]

theorem place_symm_place (E : Place c) :
    place e.symm (symm_apply e he) (place e he E) = E :=
  Place.ext (ValuationSubring.ext _ _ fun x => by
    rw [mem_place, mem_place]; simp)

theorem place_place_symm (E' : Place c') :
    place e he (place e.symm (symm_apply e he) E') = E' :=
  Place.ext (ValuationSubring.ext _ _ fun x => by
    rw [mem_place, mem_place]; simp)

end RingEquivTransport
end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair.RingEquivTransport

variable {k K K' : Type} [Field k] [Field K] [Field K']
variable {c : k →+* K} {c' : k →+* K'} (e : K ≃+* K') (he : ∀ a, e (c a) = c' a)

theorem ord_place (E : Place c) (f : K) : (place e he E).ord (e f) = E.ord f := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht' : Irreducible (ringEquiv e E.ring t) := (MulEquiv.irreducible_iff (ringEquiv e E.ring)).2 ht
  have ht0 : ((t : E.ring) : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  have key : ∀ a : E.ring, a ≠ 0 → (place e he E).ord (e a) = E.ord a := by
    intro a ha
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha ht
    have hu0 : ((u : E.ring) : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
    have h1 : (place e he E).ord (e ((u : E.ring) : K)) = 0 := by
      rw [← ringEquiv_apply e E.ring (u : E.ring)]
      exact Place.ord_eq_zero (place e he E) (u.isUnit.map (ringEquiv e E.ring))
    have h2 : (place e he E).ord (e ((t : E.ring) : K)) = 1 := by
      rw [← ringEquiv_apply e E.ring t]
      exact Place.ord_irreducible (place e he E) ht'
    have hu0' : e ((u : E.ring) : K) ≠ 0 := (map_ne_zero e).2 hu0
    have ht0' : e ((t : E.ring) : K) ≠ 0 := (map_ne_zero e).2 ht0
    push_cast
    rw [map_mul, map_pow, E.ord_mul hu0 (pow_ne_zero _ ht0), E.ord_pow, E.ord_eq_zero u.isUnit,
      E.ord_irreducible ht, Place.ord_mul _ hu0' (pow_ne_zero _ ht0'), Place.ord_pow, h1, h2]
  by_cases hf : f = 0
  · subst hf
    simp [Place.ord]
  rcases E.ring.mem_or_inv_mem f with h | h
  · exact key ⟨f, h⟩ fun h0 => hf (congrArg Subtype.val h0)
  · have := key ⟨f⁻¹, h⟩ fun h0 => hf (inv_eq_zero.1 (congrArg Subtype.val h0))
    rw [← inv_inv f, map_inv₀, Place.ord_inv, Place.ord_inv, this]

theorem constHom (E : Place c) :
    (ringEquiv e E.ring).toRingHom.comp E.const = (place e he E).const :=
  RingHom.ext fun a => Subtype.ext (he a)

theorem toRat_place (E : Place c) {n : ℕ} (ω : Forms E.const n) :
    (place e he E).toRat n (TopForm.formMap n (ringEquiv e E.ring).toRingHom (constHom e he E) ω) =
      TopForm.formMap n e.toRingHom (RingHom.ext he) (E.toRat n ω) := by
  have hτ : (e.toRingHom.comp E.ring.subtype).comp E.const = c' := RingHom.ext fun a => he a
  exact (TopForm.formMap_formMap _ (place e he E).ring.subtype (e.toRingHom.comp E.ring.subtype)
      (RingHom.ext fun _ => rfl) (constHom e he E) rfl hτ ω).trans
    (TopForm.formMap_formMap E.ring.subtype e.toRingHom _ rfl rfl (RingHom.ext he) hτ ω).symm

theorem isFormOrd_place {E : Place c} {n : ℕ} {η : Forms c n} {a : ℤ} (h : E.IsFormOrd η a) :
    (place e he E).IsFormOrd (TopForm.formMap n e.toRingHom (RingHom.ext he) η) a := by
  obtain ⟨ω, hω, f, rfl, hf⟩ := h
  refine ⟨TopForm.formMap n (ringEquiv e E.ring).toRingHom (constHom e he E) ω,
    isFreeGen_map (ringEquiv e E.ring).bijective _ (formMap_bijective _ _ n) hω,
    Units.map e.toMonoidHom f, ?_, (ord_place e he E f).trans hf⟩
  rw [map_smulₛₗ, toRat_place]
  rfl

theorem formOrd_place (E : Place c) {n : ℕ} (η : Forms c n) :
    (place e he E).formOrd (TopForm.formMap n e.toRingHom (RingHom.ext he) η) = E.formOrd η := by
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [ha.formOrd_eq, (isFormOrd_place e he ha).formOrd_eq]
  · have h' : ¬ ∃ a, (place e he E).IsFormOrd (TopForm.formMap n e.toRingHom (RingHom.ext he) η) a := by
      rintro ⟨a, ha⟩
      have := isFormOrd_place e.symm (symm_apply e he) ha
      rw [place_symm_place, formMap_symm_formMap e] at this
      exact h ⟨a, this⟩
    rw [Place.formOrd, Place.formOrd, dif_neg h, dif_neg h']

theorem ordQ_place (E : Place c) (φ : K →₀ ℚ) :
    (place e he E).ordQ (Finsupp.mapDomain e φ) = E.ordQ φ := by
  change Finsupp.linearCombination ℚ _ (Finsupp.mapDomain e φ) = Finsupp.linearCombination ℚ _ φ
  rw [Finsupp.linearCombination_mapDomain]
  have : ((fun g : K' => ((place e he E).ord g : ℚ)) ∘ e) = fun g => (E.ord g : ℚ) :=
    funext fun g => by simp only [Function.comp, ord_place]
  rw [this]

theorem disc_place (E : Place c) {n : ℕ} (η : Forms c n) (φ : K →₀ ℚ) :
    (place e he E).disc (TopForm.formMap n e.toRingHom (RingHom.ext he) η) (Finsupp.mapDomain e φ) =
      E.disc η φ := by
  rw [Place.disc, Place.disc, formOrd_place, ordQ_place]

theorem contains_place (E : Place c) (R : Subring K) :
    (place e he E).Contains (R.map e.toRingHom) ↔ E.Contains R := by
  constructor
  · intro h f hf
    exact (apply_mem_place e he E f).1 (h (e f) ⟨f, hf, rfl⟩)
  · rintro h _ ⟨f, hf, rfl⟩
    exact (apply_mem_place e he E f).2 (h f hf)

theorem isPrimeOf_place (E : Place c) (R : Subring K) :
    (place e he E).IsPrimeOf (R.map e.toRingHom) ↔ E.IsPrimeOf R := by
  refine and_congr (contains_place e he E R) ⟨fun h f hf => ?_, fun h f' hf' => ?_⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hb0, hord, hfb⟩ :=
      h (e f) ((apply_mem_place e he E f).2 hf)
    refine ⟨a, ha, b, hb, fun h0 => hb0 (by simp [h0]), ?_, ?_⟩
    · rw [← ord_place e he E]
      exact hord
    · apply e.injective
      rw [map_mul]
      exact hfb
  · obtain ⟨a, ha, b, hb, hb0, hord, hfb⟩ := h (e.symm f') ((mem_place e he E f').1 hf')
    refine ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, (map_ne_zero e).2 hb0, ?_, ?_⟩
    · rw [ord_place]
      exact hord
    · rw [← hfb, map_mul, e.apply_symm_apply]

theorem formMap_ne_zero_iff {n : ℕ} (η : Forms c n) :
    TopForm.formMap n e.toRingHom (RingHom.ext he) η ≠ 0 ↔ η ≠ 0 :=
  map_ne_zero_iff _ (formMap_bijective e (RingHom.ext he) n).1

theorem mapDomain_apply_zero (φ : K →₀ ℚ) : Finsupp.mapDomain e φ 0 = φ 0 := by
  have := Finsupp.mapDomain_apply e.injective φ 0
  rwa [map_zero] at this

theorem klt_iff {n : ℕ} (R : Subring K) (η : Forms c n) (φ : K →₀ ℚ) :
    Klt c n R η φ ↔ Klt c' n (R.map e.toRingHom) (TopForm.formMap n e.toRingHom (RingHom.ext he) η)
      (Finsupp.mapDomain e φ) := by
  unfold Klt
  rw [formMap_ne_zero_iff e he, mapDomain_apply_zero]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h E' hE' => ?_, fun h E hE => ?_⟩
  · rw [← place_place_symm e he E'] at hE' ⊢
    rw [disc_place]
    exact h _ ((contains_place e he _ R).1 hE')
  · rw [← disc_place e he]
    exact h _ ((contains_place e he E R).2 hE)

theorem effAt_iff {n : ℕ} (R : Subring K) (η : Forms c n) (φ : K →₀ ℚ) :
    EffAt c n R η φ ↔ EffAt c' n (R.map e.toRingHom) (TopForm.formMap n e.toRingHom (RingHom.ext he) η)
      (Finsupp.mapDomain e φ) := by
  unfold EffAt
  rw [formMap_ne_zero_iff e he, mapDomain_apply_zero]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h E' hE' => ?_, fun h E hE => ?_⟩
  · rw [← place_place_symm e he E'] at hE' ⊢
    rw [disc_place]
    exact h _ ((isPrimeOf_place e he _ R).1 hE')
  · rw [← disc_place e he]
    exact h _ ((isPrimeOf_place e he E R).2 hE)

include he in

theorem isLocModel_map {R : Subring K} (h : IsLocModel c R) : IsLocModel c' (R.map e.toRingHom) where
  const_mem a := ⟨c a, h.const_mem a, he a⟩
  isLocalRing := by
    haveI := h.isLocalRing
    exact (e.subringMap (s := R)).isLocalRing
  essFiniteType := by
    have h3 := h.essFiniteType.comp (RingHom.FiniteType.of_surjective
      (e.subringMap (s := R)).toRingHom (e.subringMap (s := R)).surjective).essFiniteType
    convert h3 using 1
    exact RingHom.ext fun a => Subtype.ext (he a).symm
  frac f := by
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := h.frac (e.symm f)
    refine ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, (map_ne_zero e).2 hb0, ?_⟩
    rw [← hab, map_mul, e.apply_symm_apply]

include he in
theorem isLocModel_iff (R : Subring K) : IsLocModel c R ↔ IsLocModel c' (R.map e.toRingHom) := by
  refine ⟨isLocModel_map e he, fun h => ?_⟩
  have h' := isLocModel_map e.symm (symm_apply e he) h
  have hR : (R.map e.toRingHom).map e.symm.toRingHom = R := by
    ext x
    simp [Subring.mem_map]
  rwa [hR] at h'

include he in

theorem trBasis_map {n : ℕ} {x : Fin n → K} (h : TrBasis c x) : TrBasis c' (e ∘ x) := by
  letI := c.toAlgebra
  letI := c'.toAlgebra
  exact (AlgEquiv.ofRingEquiv (f := e) he).isTranscendenceBasis h

end RingEquivTransport

theorem transport_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'),
  (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (R : Subring K) (φ : K →₀ ℚ), TrBasis c x →
  TrBasis c' (e ∘ x) ∧
  (IsLocModel c R ↔ IsLocModel c' (R.map e.toRingHom)) ∧
  (Klt c n R (dForm c x) φ ↔ Klt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) ∧
  (EffAt c n R (dForm c x) φ ↔ EffAt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) := by
  intro k K K' _ _ _ _ c c' e he n x R φ hx
  have hd : dForm c' (e ∘ x) = TopForm.formMap n e.toRingHom (RingHom.ext he) (dForm c x) :=
    (TopForm.formMap_dForm e.toRingHom (RingHom.ext he) x).symm
  rw [hd]
  exact ⟨RingEquivTransport.trBasis_map e he hx, RingEquivTransport.isLocModel_iff e he R,
    RingEquivTransport.klt_iff e he R _ φ, RingEquivTransport.effAt_iff e he R _ φ⟩

end GlobalTheory.FieldPair
