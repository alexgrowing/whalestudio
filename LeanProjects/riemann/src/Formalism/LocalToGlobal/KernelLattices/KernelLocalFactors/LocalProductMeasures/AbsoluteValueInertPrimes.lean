import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.Columns.RecLevelHost

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section One

variable {E : Type} [Field E] [NumberField E]

theorem ab_one_val {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt P a) : P.valuation E a = 1 := by
  have := Valuation.map_one_add_of_lt (v := P.valuation E) h
  rwa [add_sub_cancel] at this

theorem ab_one_one (P : HeightOneSpectrum (𝓞 E)) : OneAt P (1 : E) := by
  unfold OneAt
  rw [sub_self, map_zero]
  exact zero_lt_one

theorem ab_one_mul {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : OneAt P a) (hb : OneAt P b) : OneAt P (a * b) := by
  unfold OneAt
  have e : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ha)
  rw [map_mul, ab_one_val ha, one_mul]
  exact hb

theorem ab_one_inv {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : OneAt P a) : OneAt P a⁻¹ := by
  have h1 := ab_one_val ha
  have h0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at h1
    exact zero_ne_one h1
  unfold OneAt
  have e : a⁻¹ - 1 = -(a - 1) * a⁻¹ := by field_simp; ring
  rw [e, map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, mul_one]
  exact ha

theorem ab_one_div {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : OneAt P a) (hb : OneAt P b) : OneAt P (a / b) := by
  rw [div_eq_mul_inv]
  exact ab_one_mul ha (ab_one_inv hb)

theorem ab_one_of_mem {P : HeightOneSpectrum (𝓞 E)} {b : 𝓞 E} (h : b - 1 ∈ P.asIdeal) : OneAt P (b : E) := by
  unfold OneAt
  have : P.valuation E (algebraMap (𝓞 E) E (b - 1)) < 1 := (P.valuation_lt_one_iff_mem (K := E) (b - 1)).2 h
  rw [map_sub, map_one] at this
  exact this

theorem ab_int_exp (P : HeightOneSpectrum (𝓞 E)) {r : 𝓞 E} (hr : r ≠ 0) : ∃ k : ℕ, P.intValuation r = WithZero.exp (-(k : ℤ)) :=
  ⟨_, P.intValuation_if_neg hr⟩

theorem ab_crt {P Q : HeightOneSpectrum (𝓞 E)} (h : P ≠ Q) (k : ℕ) (t : 𝓞 E) : ∃ b : 𝓞 E, b - t ∈ P.asIdeal ^ k ∧ b - 1 ∈ Q.asIdeal := by
  have h1 : IsCoprime P.asIdeal Q.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal fun h' => h (HeightOneSpectrum.ext h')
  have h2 : IsCoprime (P.asIdeal ^ k) Q.asIdeal := h1.pow_left
  obtain ⟨e, he, e', he', hs⟩ := Ideal.isCoprime_iff_exists.1 h2
  refine ⟨t * e' + e, ?_, ?_⟩
  · have : t * e' + e - t = e * (1 - t) := by
      have : e' = 1 - e := by rw [← hs]; ring
      rw [this]; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ he
  · have : t * e' + e - 1 = e' * (t - 1) := by
      have : e = 1 - e' := by rw [← hs]; ring
      rw [this]; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ he'

theorem prime_approximation_holds : ApproxP := by
  intro E _ _ P Q h t
  obtain ⟨b, h1, h2⟩ := ab_crt h 2 t
  refine ⟨b, ?_, h1, h2⟩
  rintro rfl
  rw [zero_sub, neg_mem_iff] at h2
  exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem ab_read_int {P Q : HeightOneSpectrum (𝓞 E)} (h : P ≠ Q) {r : 𝓞 E} (hr : r ≠ 0) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ OneAt P (algebraMap (𝓞 E) E b / algebraMap (𝓞 E) E r) ∧ OneAt Q (algebraMap (𝓞 E) E b) := by
  obtain ⟨k, hk⟩ := ab_int_exp P hr
  obtain ⟨b, h1, h2⟩ := ab_crt h (k + 1) r
  have hrE : algebraMap (𝓞 E) E r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hr
  have hv : P.valuation E (algebraMap (𝓞 E) E b - algebraMap (𝓞 E) E r) < P.valuation E (algebraMap (𝓞 E) E r) := by
    have e1 : P.valuation E (algebraMap (𝓞 E) E b - algebraMap (𝓞 E) E r) = P.intValuation (b - r) := by
      rw [← map_sub]; exact P.valuation_of_algebraMap _
    have e2 : P.valuation E (algebraMap (𝓞 E) E r) = P.intValuation r := P.valuation_of_algebraMap _
    rw [e1, e2, hk]
    refine lt_of_le_of_lt ((P.intValuation_le_pow_iff_mem _ _).2 h1) ?_
    rw [WithZero.exp_lt_exp]
    push_cast
    omega
  refine ⟨b, ?_, ?_, ab_one_of_mem h2⟩
  · rintro rfl
    rw [map_zero, zero_sub, Valuation.map_neg] at hv
    exact lt_irrefl _ hv
  · unfold OneAt
    have e : algebraMap (𝓞 E) E b / algebraMap (𝓞 E) E r - 1 = (algebraMap (𝓞 E) E b - algebraMap (𝓞 E) E r) / algebraMap (𝓞 E) E r := by field_simp
    rw [e, map_div₀]
    exact (div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hrE))).2 hv

theorem ab_read {P Q : HeightOneSpectrum (𝓞 E)} (h : P ≠ Q) (a : Eˣ) : ∃ b : Eˣ, OneAt P ((b : E) / (a : E)) ∧ OneAt Q (b : E) := by
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (a : E)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hs0
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hrs
    exact a.ne_zero hrs.symm
  have hrE : algebraMap (𝓞 E) E r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hr0
  obtain ⟨b1, hb1, h11, h12⟩ := ab_read_int h hr0
  obtain ⟨b2, hb2, h21, h22⟩ := ab_read_int h hs0
  have hb1E : algebraMap (𝓞 E) E b1 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hb1
  have hb2E : algebraMap (𝓞 E) E b2 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hb2
  refine ⟨Units.mk0 _ hb1E / Units.mk0 _ hb2E, ?_, ?_⟩
  · rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, ← hrs]
    have e : algebraMap (𝓞 E) E b1 / algebraMap (𝓞 E) E b2 / (algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s) =
        (algebraMap (𝓞 E) E b1 / algebraMap (𝓞 E) E r) / (algebraMap (𝓞 E) E b2 / algebraMap (𝓞 E) E s) := by
      field_simp
    rw [e]
    exact ab_one_div h11 h21
  · rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0]
    exact ab_one_div h12 h22

theorem ab_reads (P Q : HeightOneSpectrum (𝓞 E)) (h : P ≠ Q) (x : Eˣ) : ∃ b : Eˣ, OneAt P ((b : E) / (x : E)) ∧ OneAt Q (b : E) := ab_read h x

theorem OneAt.val_eq_one {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt P a) : P.valuation E a = 1 := ab_one_val h

theorem OneAt.mul {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : OneAt P a) (hb : OneAt P b) : OneAt P (a * b) := ab_one_mul ha hb

theorem OneAt.inv {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : OneAt P a) : OneAt P a⁻¹ := ab_one_inv ha

end One

section Conj

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem ab_conj_conj (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

theorem ab_pow_conj (P : HeightOneSpectrum (𝓞 E)) (k : ℕ) {r : 𝓞 E} (h : r ∈ P.asIdeal ^ k) : cO E r ∈ (conjPrime₂ P).asIdeal ^ k := by
  have h1 : P.asIdeal.map (cO E) ≤ (conjPrime₂ P).asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, mem_conjP, cO_cO]
    exact hp
  have h2 : cO E r ∈ (P.asIdeal ^ k).map (cO E) := Ideal.mem_map_of_mem _ h
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 k h2

theorem ab_int_le (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : (conjPrime₂ P).intValuation (cO E r) ≤ P.intValuation r := by
  by_cases hr : r = 0
  · rw [hr, map_zero, map_zero, map_zero]
  · obtain ⟨k, hk⟩ := ab_int_exp P hr
    rw [hk]
    exact ((conjPrime₂ P).intValuation_le_pow_iff_mem _ _).2 (ab_pow_conj P k ((P.intValuation_le_pow_iff_mem _ _).1 hk.le))

theorem ab_int_star (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : (conjPrime₂ P).intValuation (cO E r) = P.intValuation r := by
  refine le_antisymm (ab_int_le P r) ?_
  have := ab_int_le (conjPrime₂ P) (cO E r)
  rwa [ab_conj_conj, cO_cO] at this

theorem ab_cO_coe (r : 𝓞 E) : algebraMap (𝓞 E) E (cO E r) = star (algebraMap (𝓞 E) E r) := rfl

theorem ab_val_star (P : HeightOneSpectrum (𝓞 E)) (a : E) : (conjPrime₂ P).valuation E (star a) = P.valuation E a := by
  obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  rw [← hrs, star_div₀, ← ab_cO_coe, ← ab_cO_coe, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    ab_int_star, ab_int_star]

theorem ab_one_star {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt P a) : OneAt (conjPrime₂ P) (star a) := by
  unfold OneAt at *
  have e : star a - 1 = star (a - 1) := by rw [star_sub, star_one]
  rw [e, ab_val_star]
  exact h

theorem ab_one_star' {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt (conjPrime₂ P) a) : OneAt P (star a) := by
  have := ab_one_star h
  rwa [ab_conj_conj] at this

end Conj

section Over

variable (X : Fields)

theorem ab_cO_alg (hX : X.Ok) (a : 𝓞 X.F) : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) a) = algebraMap (𝓞 X.F) (𝓞 X.E) a := by
  apply RingOfIntegers.ext
  show star (algebraMap X.F X.E (a : X.F)) = algebraMap X.F X.E (a : X.F)
  rw [hX.star_F]

theorem ab_conjP_under (hX : X.Ok) (P : HeightOneSpectrum (𝓞 X.E)) : (conjPrime₂ P).asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F) := by
  ext x
  rw [Ideal.mem_under, Ideal.mem_under, mem_conjP, ab_cO_alg X hX]

theorem ab_norm_int (hX : X.Ok) (a : 𝓞 X.E) : ∃ k : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) k = a * cO X.E a := by
  have h1 : star ((a * cO X.E a : 𝓞 X.E) : X.E) = ((a * cO X.E a : 𝓞 X.E) : X.E) := by
    show star (algebraMap (𝓞 X.E) X.E (a * cO X.E a)) = algebraMap (𝓞 X.E) X.E (a * cO X.E a)
    rw [map_mul, ab_cO_coe, star_mul', star_star, mul_comm]
  obtain ⟨k, hk⟩ := (rlh_fixed hX _).1 h1
  have hint : IsIntegral ℤ k := by
    have h2 : IsIntegral ℤ (algebraMap X.F X.E k) := by
      rw [hk]
      exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff (algebraMap X.F X.E).injective).1 h2
  refine ⟨⟨k, hint⟩, ?_⟩
  apply RingOfIntegers.ext
  exact hk

theorem local_factor_over_two : OverTwo := by
  intro X hX P P' h
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨s1, hs1, hs1'⟩ := exists_mem_notMem h1
  obtain ⟨s2, hs2, hs2'⟩ := exists_mem_notMem h2
  obtain ⟨a, ha, haP, haQ⟩ : ∃ a ∈ P'.asIdeal, a ∉ P.asIdeal ∧ a ∉ (conjPrime₂ P).asIdeal := by
    by_cases c1 : s1 ∈ (conjPrime₂ P).asIdeal
    · by_cases c2 : s2 ∈ P.asIdeal
      · refine ⟨s1 + s2, Ideal.add_mem _ hs1 hs2, ?_, ?_⟩
        · intro hm
          exact hs1' ((Ideal.add_mem_iff_left _ c2).1 hm)
        · intro hm
          exact hs2' ((Ideal.add_mem_iff_right _ c1).1 hm)
      · exact ⟨s2, hs2, c2, hs2'⟩
    · exact ⟨s1, hs1, hs1', c1⟩
  obtain ⟨k, hk⟩ := ab_norm_int X hX a
  have hk1 : k ∈ P'.asIdeal.under (𝓞 X.F) := by
    rw [Ideal.mem_under, hk]
    exact Ideal.mul_mem_right _ _ ha
  rw [h, Ideal.mem_under, hk] at hk1
  rcases P.isPrime.mem_or_mem hk1 with h3 | h3
  · exact haP h3
  · exact haQ ((mem_conjP P a).2 h3)

end Over

section Main

theorem absolute_value_split_primes : AbsSplit := by
  intro X hX A _ lam Rm hL v P hP hne x b hbQ hbP
  have hne' : P ≠ conjPrime₂ P := fun h => hne h.symm
  obtain ⟨b1, h11, h12⟩ := ab_read hne' x
  obtain ⟨b2, h21, h22⟩ := ab_read hne' (star x)
  rw [Units.coe_star] at h21
  have hover : ∀ P' : HeightOneSpectrum (𝓞 X.E), P'.asIdeal.under (𝓞 X.F) = v.asIdeal → P' = P ∨ P' = conjPrime₂ P :=
    fun P' h => local_factor_over_two X hX P P' (h.trans hP.symm)
  have key : ∀ y : X.Eˣ, OneAt P (y : X.E) → OneAt (conjPrime₂ P) (y : X.E) → lam v y = 1 := fun y h1 h2 =>
    hL.wild v y fun P' h' => by
      rcases hover P' h' with h | h
      · rw [h]; exact h1
      · rw [h]; exact h2
  have hx0 : (x : X.E) ≠ 0 := x.ne_zero
  have hsx0 : star (x : X.E) ≠ 0 := star_ne_zero.2 hx0
  have hb10 : (b1 : X.E) ≠ 0 := b1.ne_zero
  have hb20 : (b2 : X.E) ≠ 0 := b2.ne_zero
  have hsb20 : star (b2 : X.E) ≠ 0 := star_ne_zero.2 hb20
  have hb0 : (b : X.E) ≠ 0 := b.ne_zero
  have s1 : lam v (x / (b1 * star b2)) = 1 := by
    apply key
    · rw [Units.val_div_eq_div_val, Units.val_mul, Units.coe_star]
      have e : (x : X.E) / ((b1 : X.E) * star (b2 : X.E)) = ((b1 : X.E) / (x : X.E))⁻¹ * (star (b2 : X.E))⁻¹ := by field_simp
      rw [e]
      exact ab_one_mul (ab_one_inv h11) (ab_one_inv (ab_one_star' h22))
    · rw [Units.val_div_eq_div_val, Units.val_mul, Units.coe_star]
      have e : (x : X.E) / ((b1 : X.E) * star (b2 : X.E)) = (b1 : X.E)⁻¹ * star (((b2 : X.E) / star (x : X.E))⁻¹) := by
        rw [star_inv₀, star_div₀, star_star, inv_div]
        field_simp
      rw [e]
      exact ab_one_mul (ab_one_inv h12) (ab_one_star (ab_one_inv h21))
  have s2 : lam v (b2 * star b2) = 1 := by
    have hfix : star ((b2 : X.E) * star (b2 : X.E)) = (b2 : X.E) * star (b2 : X.E) := by
      rw [star_mul', star_star, mul_comm]
    obtain ⟨k, hk⟩ := (rlh_fixed hX _).1 hfix
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [map_zero] at hk
      exact (mul_ne_zero hb20 hsb20) hk.symm
    have e : b2 * star b2 = Units.map (algebraMap X.F X.E).toMonoidHom (Units.mk0 k hk0) := by
      apply Units.ext
      rw [Units.val_mul, Units.coe_star]
      exact hk.symm
    rw [e]
    exact hL.trivF v _
  have s3 : lam v (b / (b1 / b2)) = 1 := by
    apply key
    · rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val]
      have e : (b : X.E) / ((b1 : X.E) / (b2 : X.E)) =
          ((b : X.E) / ((x : X.E) / star (x : X.E))) * (((b1 : X.E) / (x : X.E))⁻¹ * ((b2 : X.E) / star (x : X.E))) := by field_simp
      rw [e]
      exact ab_one_mul hbP (ab_one_mul (ab_one_inv h11) h21)
    · rw [Units.val_div_eq_div_val, Units.val_div_eq_div_val]
      exact ab_one_div hbQ (ab_one_div h12 h22)
  rw [map_div, map_mul, div_eq_one] at s1
  rw [map_mul] at s2
  rw [map_div, map_div, div_eq_one] at s3
  rw [s1, s3, eq_inv_of_mul_eq_one_right s2, div_eq_mul_inv]

theorem absolute_value_inert_primes : AbsInert := by
  intro X hX A _ lam Rm hL v P hP hc hv hun x
  have hover : ∀ P' : HeightOneSpectrum (𝓞 X.E), P'.asIdeal.under (𝓞 X.F) = v.asIdeal → P' = P := fun P' h => by
    rcases local_factor_over_two X hX P P' (h.trans hP.symm) with h | h
    · exact h
    · rw [h, hc]
  obtain ⟨p, hpv, hp2⟩ : ∃ p ∈ P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)), algebraMap (𝓞 X.F) (𝓞 X.E) p ∉ P.asIdeal ^ 2 := by
    by_contra hcon
    push Not at hcon
    exact hun (Ideal.map_le_iff_le_comap.2 fun p hp => hcon p hp)
  have hpP : algebraMap (𝓞 X.F) (𝓞 X.E) p ∈ P.asIdeal ^ 1 := by rw [pow_one]; exact hpv
  have hpE0 : algebraMap (𝓞 X.F) (𝓞 X.E) p ≠ 0 := by
    intro h0
    rw [h0] at hp2
    exact hp2 (zero_mem _)
  have hp0 : (algebraMap (𝓞 X.F) X.F p) ≠ 0 := by
    intro h0
    apply hpE0
    have : p = 0 := (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 X.F) X.F)).1 h0
    rw [this, map_zero]
  obtain ⟨k, hk⟩ := ab_int_exp P hpE0
  have hk1 : k = 1 := by
    have h1 := (P.intValuation_le_pow_iff_mem _ _).2 hpP
    have h2 : ¬ P.intValuation (algebraMap (𝓞 X.F) (𝓞 X.E) p) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
      hp2 ((P.intValuation_le_pow_iff_mem _ _).1 h)
    rw [hk, WithZero.exp_le_exp] at h1 h2
    push_cast at h1 h2
    omega
  let U : X.Eˣ := Units.map (algebraMap X.F X.E).toMonoidHom (Units.mk0 _ hp0)
  have hU : P.valuation X.E (U : X.E) = WithZero.exp (-1 : ℤ) := by
    have e : (U : X.E) = algebraMap (𝓞 X.E) X.E (algebraMap (𝓞 X.F) (𝓞 X.E) p) :=
      (IsScalarTower.algebraMap_apply (𝓞 X.F) X.F X.E p).symm.trans (IsScalarTower.algebraMap_apply (𝓞 X.F) (𝓞 X.E) X.E p)
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, hk, hk1]
    rfl
  have hx0 : P.valuation X.E (x : X.E) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  have h1 : lam v (x * U ^ (WithZero.log (P.valuation X.E (x : X.E)))) = 1 := by
    apply hL.unr v hv
    intro P' hP'
    rw [hover P' hP', Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hU, ← WithZero.exp_zsmul]
    conv_lhs => rw [← WithZero.exp_log hx0]
    rw [← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
    simp
  rw [map_mul, map_zpow, hL.trivF v _, one_zpow, mul_one] at h1
  exact h1

end Main

end Formalism.L2.Ker
