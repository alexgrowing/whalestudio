import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntRing
open IsDedekindDomain GlobalTheory.TauNorm Polynomial
open scoped TensorProduct

namespace GlobalTheory.FinRingNorm

theorem field_case (F : Type) [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (d s : F) (hd : d ≠ 0) :
    ∃ a b : F, a ^ 2 - d * b ^ 2 = s := by
  classical
  cases nonempty_fintype F
  have hc : ringChar F ≠ 2 := by
    intro h; apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this; exact_mod_cast this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F) (f := X ^ 2)
    (g := -(C d * X ^ 2) - C s) (by simp) (by compute_degree!) (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨a, b, ?_⟩
  simp only [eval_pow, eval_X, eval_sub, eval_neg, eval_mul, eval_C] at hab
  linear_combination hab

theorem reduced_case (S : Type) [CommRing S] [Finite S] [IsReduced S] (h2 : IsUnit (2 : S))
    (d s : S) (hd : IsUnit d) : ∃ a b : S, a ^ 2 - d * b ^ 2 = s := by
  classical
  have key : ∀ I : MaximalSpectrum S, ∃ a b : S ⧸ I.asIdeal,
      a ^ 2 - (Ideal.Quotient.mk I.asIdeal d) * b ^ 2 = Ideal.Quotient.mk I.asIdeal s := by
    intro I
    letI : Field (S ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (S ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    have h2' : (2 : S ⧸ I.asIdeal) ≠ 0 := by
      have := (h2.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
      rwa [map_ofNat] at this
    exact field_case _ h2' _ _ (hd.map (Ideal.Quotient.mk I.asIdeal)).ne_zero
  choose A B hAB using key
  refine ⟨(IsArtinianRing.equivPi S).symm A, (IsArtinianRing.equivPi S).symm B, ?_⟩
  apply (IsArtinianRing.equivPi S).injective
  funext I
  simp only [map_sub, map_mul, map_pow, AlgEquiv.apply_symm_apply, Pi.sub_apply, Pi.mul_apply,
    Pi.pow_apply]
  exact hAB I

theorem finiteRing_sq_sub_mul_sq_eq_of_card (n : ℕ) : ∀ (S : Type) [CommRing S] [Finite S], Nat.card S = n → IsUnit (2 : S) →
    ∀ d s : S, IsUnit d → IsUnit s → ∃ a b : S, a ^ 2 - d * b ^ 2 = s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn h2 d s hd hs
  by_cases hred : IsReduced S
  · exact reduced_case S h2 d s hd

  obtain ⟨x, hx0, hx2⟩ : ∃ x : S, x ≠ 0 ∧ x ^ 2 = 0 := by
    rw [isReduced_iff] at hred
    push_neg at hred
    obtain ⟨y, ⟨k, hk⟩, hy⟩ := hred
    classical
    have hex : ∃ m, y ^ m = 0 := ⟨k, hk⟩
    let m := Nat.find hex
    have hm : y ^ m = 0 := Nat.find_spec hex
    have hm0 : m ≠ 0 := by
      intro h
      have : y ^ m = 1 := by rw [h, pow_zero]
      apply hy
      rw [← mul_one y, ← this, hm, mul_zero]
    have hm1 : m ≠ 1 := by
      intro h; apply hy; rw [← pow_one y, ← h, hm]
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨y ^ j, ?_, ?_⟩
    · exact Nat.find_min hex (by omega)
    · rw [← pow_mul]
      obtain ⟨t, ht⟩ : ∃ t, j * 2 = m + t := ⟨j * 2 - m, by omega⟩
      rw [ht, pow_add, hm, zero_mul]
  set I : Ideal S := Ideal.span {x} with hI
  have hlt : Nat.card (S ⧸ I) < n := by
    rw [← hn]
    classical
    cases nonempty_fintype S
    haveI : Finite (S ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    cases nonempty_fintype (S ⧸ I)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_surjective_not_injective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    intro hinj
    apply hx0
    apply hinj
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  haveI : Finite (S ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨a', b', hab'⟩ := ih _ hlt (S ⧸ I) rfl (h2.map (Ideal.Quotient.mk I)) _ _
    (hd.map (Ideal.Quotient.mk I)) (hs.map (Ideal.Quotient.mk I))
  obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b'
  have hmem : a0 ^ 2 - d * b0 ^ 2 - s ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow]
    rw [hab', sub_self]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  obtain ⟨t, ht⟩ := hs.exists_right_inv
  set iv := t - t ^ 2 * r * x with hiv
  have hv : (s + r * x) * iv - 1 = 0 := by
    rw [hiv]; linear_combination (1 - t * r * x) * ht - t ^ 2 * r ^ 2 * hx2
  refine ⟨a0 - r * a0 * iv * u * x, b0 - r * b0 * iv * u * x, ?_⟩
  linear_combination (1 - r * x * 2 * u * iv) * hr.symm - r * x * 2 * u * hv - r * x * hu + (r * iv * u) ^ 2 * (a0 ^ 2 - d * b0 ^ 2) * hx2

theorem exists_sq_sub_mul_sq_eq : ∀ (S : Type) [CommRing S] [Finite S], IsUnit (2 : S) →
    ∀ d s : S, IsUnit d → IsUnit s → ∃ a b : S, a ^ 2 - d * b ^ 2 = s :=
  fun S _ _ h2 d s hd hs => finiteRing_sq_sub_mul_sq_eq_of_card _ S rfl h2 d s hd hs

end GlobalTheory.FinRingNorm
