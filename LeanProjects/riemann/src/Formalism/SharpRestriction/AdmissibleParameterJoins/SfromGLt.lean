import Mathlib

noncomputable section

namespace Formalism.MainNotions.J

open Ideal NumberField IsDedekindDomain

section Split

variable (K : Type) [Field K] [NumberField K] (p : ℕ)

theorem pI_ne_bot (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

theorem pI_max (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

theorem liesOver_ne_bot (hp : p.Prime) (I : Ideal (𝓞 K)) (hI : I.LiesOver (span {(p : ℤ)})) : I ≠ ⊥ := by
  intro h
  have h1 : (span {(p : ℤ)} : Ideal ℤ) = I.under ℤ := hI.over
  rw [h, Ideal.under, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at h1
  exact pI_ne_bot p hp h1

theorem img_places (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} =
      (span {(p : ℤ)}).primesOver (𝓞 K) := by
  haveI := pI_max p hp
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hle : (span {(p : ℤ)} : Ideal ℤ) ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ v.asIdeal
      simpa using hv
    exact (pI_max p hp).eq_of_le (v.isPrime.comap (algebraMap ℤ (𝓞 K))).ne_top hle
  · rintro ⟨hPp, hPl⟩
    refine ⟨⟨P, hPp, liesOver_ne_bot K p hp P hPl⟩, ?_, rfl⟩
    have h1 : (p : ℤ) ∈ P.under ℤ := by
      rw [← hPl.over]
      exact Ideal.mem_span_singleton_self _
    simpa using h1

theorem ncard_places (hp : p.Prime) :
    ({v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}).ncard =
      (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card := by
  haveI := pI_max p hp
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset (pI_ne_bot p hp), ← img_places K p hp,
    Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

theorem map_pI_ne_bot (hp : p.Prime) : map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≠ ⊥ := by
  rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot, map_natCast]
  exact_mod_cast hp.ne_zero

theorem ef_pos (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)) :
    1 ≤ (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P := by
  haveI := pI_max p hp
  obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hP
  have he : 0 < (span {(p : ℤ)}).ramificationIdx' P := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (pI_ne_bot p hp)]
    exact Ideal.ramificationIdx_pos P ℤ
  have hf : 0 < (span {(p : ℤ)}).inertiaDeg' P := Ideal.inertiaDeg'_pos _ _
  exact Nat.mul_pos he hf

theorem sum_ef (hp : p.Prime) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = Module.finrank ℚ K := by
  haveI := pI_max p hp
  exact Ideal.sum_ramification_inertia (𝓞 K) ℚ K (pI_ne_bot p hp)

theorem ef_one_of_card (hp : p.Prime)
    (h : (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1 := by
  intro P hP
  have h1 : ∑ _Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K), 1 =
      ∑ Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
        (span {(p : ℤ)}).ramificationIdx' Q * (span {(p : ℤ)}).inertiaDeg' Q := by
    rw [sum_ef K p hp, ← h, Finset.sum_const, smul_eq_mul, mul_one]
  exact ((Finset.sum_eq_sum_iff_of_le (fun Q hQ => ef_pos K p hp Q hQ)).mp h1 P hP).symm

theorem card_of_ef_one (hp : p.Prime)
    (h : ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1) :
    (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K := by
  rw [← sum_ef K p hp, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_one]

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem ef_one_sub (hp : p.Prime)
    (hL : ∀ Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L),
      (span {(p : ℤ)}).ramificationIdx' Q * (span {(p : ℤ)}).inertiaDeg' Q = 1) :
    ∀ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = 1 := by
  intro P hP
  haveI := pI_max p hp
  obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hP
  have hPne : P ≠ ⊥ := liesOver_ne_bot K p hp P hPl
  haveI : P.IsMaximal := hPp.isMaximal hPne

  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) P
  haveI := hQl
  haveI hQp : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  have hQ : Q ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 L)).mpr ⟨hQm.isPrime, hQp⟩
  have h1 := hL Q hQ
  have hmapP : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P ≠ ⊥ := by
    intro h
    apply hPne
    have h2 : P ≤ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P).comap (algebraMap (𝓞 K) (𝓞 L)) := Ideal.le_comap_map
    rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))] at h2
    exact le_bot_iff.mp h2
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) P ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hQl.over
  have he := Ideal.ramificationIdx'_algebra_tower (p := span {(p : ℤ)}) (P := P) (Q := Q) hmapP
    (map_pI_ne_bot L p hp) hle
  have hf := Ideal.inertiaDeg'_algebra_tower (span {(p : ℤ)}) P Q
  rw [he, hf] at h1
  have h3 : ((span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P) *
      (P.ramificationIdx' Q * P.inertiaDeg' Q) = 1 := by
    rw [← h1]
    ring
  exact Nat.eq_one_of_mul_eq_one_right h3

theorem splits_sub (hp : p.Prime)
    (h : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L) :
    Nat.card {v : HeightOneSpectrum (𝓞 K) // ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} = Module.finrank ℚ K ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  haveI := pI_max p hp
  have hL : (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 L)).card = Module.finrank ℚ L := by
    rw [← ncard_places L p hp]
    exact h
  have hefK := ef_one_sub K p L hp (ef_one_of_card L p hp hL)
  refine ⟨?_, ?_⟩
  · rw [← card_of_ef_one K p hp hefK, ← ncard_places K p hp]
    exact Nat.card_coe_set_eq _
  · intro v hv
    have hmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K) := by
      rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset (pI_ne_bot p hp), ← img_places K p hp]
      exact ⟨v, hv, rfl⟩
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hmem
    have hf1 : (span {(p : ℤ)}).inertiaDeg' v.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_left (hefK _ hmem)
    have hn := Ideal.absNorm_eq_pow_inertiaDeg' (R := 𝓞 K) (p := p) v.asIdeal hp
    rw [hf1, pow_one] at hn
    rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Split

end Formalism.MainNotions.J

end
