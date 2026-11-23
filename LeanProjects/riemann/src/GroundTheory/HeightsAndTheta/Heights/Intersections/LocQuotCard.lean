import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

theorem isLocalization_of_mem_iff {O F : Type*} [CommRing O] [Field F] (φ : O →+* F) (hφ : Function.Injective φ)
    (L : Subring F) [Algebra O L] (hL : ∀ x : O, ((algebraMap O L x : L) : F) = φ x) (m : Ideal O) [m.IsPrime]
    (h : ∀ y : F, y ∈ L ↔ ∃ x s : O, s ∉ m ∧ y * φ s = φ x) :
    IsLocalization.AtPrime L m where
  map_units := by
    rintro ⟨s, hs⟩
    have hs0 : φ s ≠ 0 := fun h0 => hs (by rw [(map_eq_zero_iff φ hφ).1 h0]; exact m.zero_mem)
    refine IsUnit.of_mul_eq_one ⟨(φ s)⁻¹, (h _).2 ⟨1, s, hs, by rw [map_one, inv_mul_cancel₀ hs0]⟩⟩ ?_
    apply Subtype.ext
    simp only [Subring.coe_mul, hL, Subring.coe_one]
    exact mul_inv_cancel₀ hs0
  surj z := by
    obtain ⟨x, s, hs, hxs⟩ := (h z).1 z.2
    exact ⟨⟨x, ⟨s, hs⟩⟩, Subtype.ext (by simp only [Subring.coe_mul, hL]; exact hxs)⟩
  exists_of_eq {x y} hxy := ⟨1, by
    have h1 := congrArg Subtype.val hxy
    rw [hL, hL] at h1
    rw [hφ h1]⟩

theorem card_quot_map_eq_card_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (p : Ideal (R ⧸ I)) [p.IsPrime] [IsLocalization.AtPrime S (p.comap (Ideal.Quotient.mk I))] :
    Nat.card (S ⧸ I.map (algebraMap R S)) = Nat.card (Localization.AtPrime p) := by
  have hM : Algebra.algebraMapSubmonoid (R ⧸ I) (p.comap (Ideal.Quotient.mk I)).primeCompl = p.primeCompl := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨r', hr', he⟩
      rw [← he]
      exact hr'
    · intro hx
      exact ⟨r, hx, rfl⟩
  have : IsLocalization p.primeCompl (S ⧸ I.map (algebraMap R S)) := hM ▸ inferInstance
  exact Nat.card_congr (IsLocalization.algEquiv p.primeCompl _ (Localization.AtPrime p)).toEquiv

theorem card_quot_span_eq_card_localization {O L : Type*} [CommRing O] [CommRing L] (ψ : O →+* L) (b : O)
    (m : Ideal O) [m.IsPrime] (p : Ideal (O ⧸ Ideal.span {b})) [p.IsPrime]
    (hm : m = p.comap (Ideal.Quotient.mk _)) (h : @IsLocalization O _ m.primeCompl L _ ψ.toAlgebra) :
    Nat.card (L ⧸ Ideal.span {ψ b}) = Nat.card (Localization.AtPrime p) := by
  subst hm
  let _ := ψ.toAlgebra
  rw [← card_quot_map_eq_card_localization (S := L) (Ideal.span {b}) p, Ideal.map_span, Set.image_singleton,
    RingHom.algebraMap_toAlgebra]

theorem log_card_eq_sum_log_card_localization (A : Type*) [CommRing A] [Finite A] [Fintype (PrimeSpectrum A)] :
    Real.log (Nat.card A) = ∑ p : PrimeSpectrum A, Real.log (Nat.card (Localization.AtPrime p.asIdeal)) := by
  have hA : Nat.card A = ∏ p : PrimeSpectrum A, Nat.card (Localization.AtPrime p.asIdeal) := by
    rw [Nat.card_congr (PrimeSpectrum.toPiLocalizationEquiv A).toEquiv, Nat.card_pi]
  have h0 : Nat.card A ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  rw [hA, Finset.prod_ne_zero_iff] at h0
  rw [hA, Nat.cast_prod, Real.log_prod fun p _ => by exact_mod_cast h0 p (Finset.mem_univ _)]

theorem finsum_mem_eq_sum_of_injective {α β : Type*} [Fintype β] (s : Set α) (f : α → ℝ) (g : β → α)
    (hg : Function.Injective g) (hs : ∀ x, g x ∈ s) (hf : ∀ a ∈ s, f a ≠ 0 → a ∈ Set.range g) :
    ∑ᶠ a ∈ s, f a = ∑ x, f (g x) := by
  have hS : s ∩ Function.support f = Set.range g ∩ Function.support f := by
    ext a
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hf a h1 h2, h2⟩
    · rintro ⟨⟨x, rfl⟩, h2⟩
      exact ⟨hs x, h2⟩
  rw [← finsum_mem_inter_support, hS, finsum_mem_inter_support, finsum_mem_range hg, finsum_eq_sum_of_fintype]

end GroundTheory.Heights₂.Heights.Inter
