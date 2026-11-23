import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentIsUnitOneAddOrSubAdeleStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

theorem hilbert90_involution_of_idempotent_unit {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (u d e s : R) (hu : u * σ u = 1) (hd : σ d = -d) (hdu : IsUnit d) (h2 : IsUnit (2 : R))
    (he : e * e = e) (hσe : σ e = e) (hs : u + σ u = 2 * s)
    (hun : IsUnit (e * (1 + s) + (1 - e) * (1 - s))) :
    ∃ x : Rˣ, (x : R) = u * σ x := by
  obtain ⟨d', hd'⟩ := hdu.exists_right_inv
  have h3 : IsUnit (e - (1 - e) * d ^ 2) := by
    refine IsUnit.of_mul_eq_one (e - (1 - e) * d' ^ 2) ?_
    have h : d ^ 2 * d' ^ 2 = 1 := by rw [← mul_pow, hd', one_pow]
    linear_combination (1 + d ^ 2 + d' ^ 2 + d ^ 2 * d' ^ 2) * he + (1 - e) * h
  have hx : σ (e * (1 + u) + (1 - e) * d * (1 - u)) = e * (1 + σ u) - (1 - e) * d * (1 - σ u) := by
    simp only [map_add, map_mul, map_sub, map_one, hσe, hd]; ring
  have hN : (e * (1 + u) + (1 - e) * d * (1 - u)) * (e * (1 + σ u) - (1 - e) * d * (1 - σ u)) =
      2 * (e * (1 + s) + (1 - e) * (1 - s)) * (e - (1 - e) * d ^ 2) := by
    have hv : σ u = 2 * s - u := by linear_combination hs
    rw [hv] at hu ⊢
    have h1 : e * (1 - e) = 0 := by linear_combination - he
    have h4 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
    generalize 1 - e = f at h1 h4 ⊢
    linear_combination (e * e - f * f * d ^ 2) * hu +
      (d * ((1 - u) * (1 + (2 * s - u)) - (1 + u) * (1 - (2 * s - u))) + 2 * (1 + s) * d ^ 2 - 2 * (1 - s)) * h1
  have hxu : IsUnit (e * (1 + u) + (1 - e) * d * (1 - u)) :=
    isUnit_of_mul_isUnit_left (hN ▸ (h2.mul hun).mul h3)
  refine ⟨hxu.unit, ?_⟩
  rw [IsUnit.unit_spec, hx]
  linear_combination (- e - (1 - e) * d) * hu

theorem aut_eq_one_or_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (g : E ≃ₐ[F] E) : g = 1 ∨ g = c := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  by_contra hg
  push Not at hg
  obtain ⟨x, -, hx⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact hg.2 ((hx g hg.1).trans (hx c hc).symm)

theorem hilbert90_adeleRing_tensor_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → ∀ u : AdeleRing (𝓞 F) F ⊗[F] E, u * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c (x : AdeleRing (𝓞 F) F ⊗[F] E) := by
  intro F E _ _ _ _ _ c h2 hc u hu
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcc : ∀ x, c (c x) = x := by
    intro x
    rcases aut_eq_one_or_of_finrank_two c h2 hc (c * c) with h | h
    · simpa using congrArg (fun g : E ≃ₐ[F] E => g x) h
    · exact absurd (by simpa using h) hc
  have htr : ∀ x : E, ∃ t : F, x + c x = algebraMap F E t := by
    intro x
    have : x + c x ∈ Set.range (algebraMap F E) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro g
      rcases aut_eq_one_or_of_finrank_two c h2 hc g with rfl | rfl
      · rfl
      · rw [map_add, hcc, add_comm]
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht.symm⟩
  have hsg : ∀ (a : AdeleRing (𝓞 F) F) (x : E), sg (AdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by
    intro a x; simp [sg]
  have hσ : ∀ z, sg (AdeleRing (𝓞 F) F) c (sg (AdeleRing (𝓞 F) F) c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [hsg, hsg, hcc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hT : ∀ z, ∃ t : AdeleRing (𝓞 F) F, z + sg (AdeleRing (𝓞 F) F) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      rw [hsg, ← TensorProduct.tmul_add, ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  obtain ⟨t, ht⟩ := hT u
  obtain ⟨e, he, hun⟩ := GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele F ((2 : F)⁻¹ • t)
  let ι : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F) F ⊗[F] E := Algebra.TensorProduct.includeLeftRingHom
  have hι : ∀ a, ι a = a ⊗ₜ 1 := fun a => rfl
  let κ : E →ₐ[F] AdeleRing (𝓞 F) F ⊗[F] E := Algebra.TensorProduct.includeRight
  have hκ : ∀ a, κ a = 1 ⊗ₜ a := fun a => rfl
  refine hilbert90_involution_of_idempotent_unit (sg (AdeleRing (𝓞 F) F) c : _ →+* _) hσ u (κ (y - c y)) (ι e)
    (ι ((2 : F)⁻¹ • t)) hu ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change sg _ c _ = _
    rw [← map_neg, hκ, hκ, hsg, map_sub, hcc, neg_sub]
  · exact (IsUnit.mk0 _ (sub_ne_zero.2 hy.symm)).map κ
  · have := (IsUnit.mk0 (2 : E) two_ne_zero).map κ
    rwa [map_ofNat] at this
  · rw [← map_mul, he]
  · change sg _ c _ = _
    rw [hι, hsg, map_one]
  · change u + sg _ c u = _
    rw [ht, two_mul, ← map_add, ← add_smul, hι]
    norm_num
  · have := hun.map ι
    simpa only [map_add, map_mul, map_sub, map_one] using this

end GlobalTheory.AdLat
