import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

def μc (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma μc_prim (q : ℕ) [NeZero q] : IsPrimitiveRoot (μc q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    aeval x (cyclotomic n ℤ) = eval x (cyclotomic n R) := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

lemma transfer {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (P : ℤ[X])
    (hP : aeval (μc q) P = 0) : aeval ζ.1 P = 0 := by
  have hμ := μc_prim q
  have h1 : cyclotomic q ℤ = minpoly ℤ (μc q) := cyclotomic_eq_minpoly hμ (NeZero.pos q)
  have hd : cyclotomic q ℤ ∣ P := h1 ▸ minpoly.isIntegrallyClosed_dvd (hμ.isIntegral (NeZero.pos q)) hP
  obtain ⟨Q, rfl⟩ := hd
  rw [map_mul, ζ.2.2, zero_mul]

lemma transfer2 {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (F : (ℤ[X])[X])
    (hF : F.map (aeval (μc q)).toRingHom = 0) : F.map (aeval ζ.1).toRingHom = 0 := by
  ext k
  rw [coeff_map, coeff_zero]
  apply transfer ζ
  have := congrArg (fun G => coeff G k) hF
  simpa [coeff_map] using this

lemma nthRoots_eq (q : ℕ) [NeZero q] :
    nthRootsFinset q (1 : ℂ) = (Finset.range q).image (fun a => μc q ^ a) := by
  have hμ := μc_prim q
  ext z
  rw [mem_nthRootsFinset (NeZero.pos q), Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hz
    exact ⟨i, Finset.mem_range.2 hi, rfl⟩
  · rintro ⟨a, -, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]

lemma primRoots_eq (q : ℕ) [NeZero q] :
    primitiveRoots q ℂ = ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => μc q ^ a) := by
  have hμ := μc_prim q
  ext z
  rw [mem_primitiveRoots (NeZero.pos q), Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hz.pow_eq_one
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, (hμ.pow_iff_coprime (NeZero.pos q) i).1 hz⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact hμ.pow_of_coprime a (Finset.mem_filter.1 ha).2

lemma injOn (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ Finset.range q) :
    Set.InjOn (fun a => μc q ^ a) s := by
  intro i hi j hj h
  exact (μc_prim q).pow_inj (Finset.mem_range.1 (hs hi)) (Finset.mem_range.1 (hs hj)) h

lemma C_prod_range (q : ℕ) [NeZero q] :
    ∏ a ∈ Finset.range q, (X - C (μc q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (μc_prim q), nthRoots_eq,
    Finset.prod_image (injOn q _ (subset_refl _))]

lemma C_prod_coprime (q : ℕ) [NeZero q] :
    ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C (μc q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (μc_prim q), primRoots_eq,
    Finset.prod_image (injOn q _ (Finset.filter_subset _ _))]

lemma C_prod_erase (q : ℕ) [NeZero q] :
    ∏ a ∈ (Finset.range q).erase 0, (X - C (μc q ^ a)) = ∑ i ∈ Finset.range q, (X ^ i : ℂ[X]) := by
  have h0 : 0 ∈ Finset.range q := Finset.mem_range.2 (NeZero.pos q)
  have h := Finset.mul_prod_erase (Finset.range q) (fun a => (X - C (μc q ^ a) : ℂ[X])) h0
  have hne : (X - C (1 : ℂ) : ℂ[X]) ≠ 0 := X_sub_C_ne_zero 1
  apply mul_left_cancel₀ hne
  calc (X - C (1 : ℂ)) * ∏ a ∈ (Finset.range q).erase 0, (X - C (μc q ^ a))
      = ∏ a ∈ Finset.range q, (X - C (μc q ^ a)) := by simpa only [pow_zero] using h
    _ = X ^ q - 1 := C_prod_range q
    _ = (X - C (1 : ℂ)) * ∑ i ∈ Finset.range q, (X ^ i : ℂ[X]) := by
        rw [map_one, mul_comm, geom_sum_mul]

end GlobalTheory.EtC.PrimBasic

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

lemma prim_pow_q {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := transfer ζ (X ^ q - 1) (by simp [(μc_prim q).pow_eq_one])
  simpa [sub_eq_zero] using h

lemma prod_range {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ Finset.range q, (X - C (ζ.1 ^ a)) = (X ^ q - 1 : A[X]) := by
  have h := transfer2 ζ (∏ a ∈ Finset.range q, (X - C X ^ a) - (X ^ q - 1 : (ℤ[X])[X])) (by
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_range, sub_self])
  simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  simpa only [← C_pow, sub_eq_zero] using h

lemma prod_coprime {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C (ζ.1 ^ a)) = cyclotomic q A := by
  have h := transfer2 ζ (∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C X ^ a)
      - cyclotomic q (ℤ[X])) (by
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_coprime, sub_self])
  simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  simpa only [← C_pow, sub_eq_zero] using h

lemma prod_erase {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ (Finset.range q).erase 0, (1 - ζ.1 ^ a) = (q : A) := by
  have h := transfer2 ζ (∏ a ∈ (Finset.range q).erase 0, (X - C X ^ a) - ∑ i ∈ Finset.range q, (X ^ i : (ℤ[X])[X])) (by
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_erase, sub_self])
  simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  have h2 := congrArg (eval (1 : A)) h
  simp only [eval_sub, eval_prod, eval_finset_sum, eval_X, eval_C, eval_pow, one_pow, eval_zero,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, sub_eq_zero] at h2
  simpa [← C_pow] using h2

end GlobalTheory.EtC.PrimBasic

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

lemma isUnit_one_sub {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (c : ℕ)
    (hc : c % q ≠ 0) : IsUnit (1 - ζ.1 ^ c) := by
  have hmem : c % q ∈ (Finset.range q).erase 0 :=
    Finset.mem_erase.2 ⟨hc, Finset.mem_range.2 (Nat.mod_lt _ (NeZero.pos q))⟩
  have hd : (1 - ζ.1 ^ (c % q)) ∣ (q : A) :=
    (Finset.dvd_prod_of_mem (fun a => 1 - ζ.1 ^ a) hmem).trans (dvd_of_eq (prod_erase ζ))
  rw [pow_eq_pow_mod c (prim_pow_q ζ)]
  exact isUnit_of_dvd_unit hd ζ.2.1

lemma isUnit_val {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 := by
  refine isUnit_iff_exists_inv.2 ⟨ζ.1 ^ (q - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), prim_pow_q ζ]

lemma isUnit_pow_sub_pow_of_le {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (a b : ℕ)
    (hab : ¬ a ≡ b [MOD q]) (hle : b ≤ a) : IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hd : d % q ≠ 0 := by
    intro h0
    apply hab
    exact (Nat.modEq_iff_dvd' hle).2 (by simpa using Nat.dvd_of_mod_eq_zero h0) |>.symm
  have e : ζ.1 ^ (b + d) - ζ.1 ^ b = -(ζ.1 ^ b * (1 - ζ.1 ^ d)) := by ring
  rw [e]
  exact (((isUnit_val ζ).pow b).mul (isUnit_one_sub ζ d hd)).neg

theorem prim_basic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r) := by
  intro q _ A _
  refine ⟨fun ζ => prim_pow_q ζ, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    have h : aeval (ζ.1 ^ a) (cyclotomic q ℤ) = 0 := by
      rw [← aeval_X_pow (R := ℤ), ← aeval_comp]
      apply transfer ζ
      rw [aeval_comp, aeval_X_pow, aeval_cyc]
      exact ((μc_prim q).pow_of_coprime a ha).isRoot_cyclotomic (NeZero.pos q)
    exact ⟨(⟨ζ.1 ^ a, ζ.2.1, h⟩ : {z : A // IsUnit (q : A) ∧ aeval z (cyclotomic q ℤ) = 0}), rfl⟩
  · intro ζ a b hab
    rcases le_total b a with hle | hle
    · exact isUnit_pow_sub_pow_of_le ζ a b hab hle
    · have := isUnit_pow_sub_pow_of_le ζ b a (fun h => hab h.symm) hle
      have e : ζ.1 ^ a - ζ.1 ^ b = -(ζ.1 ^ b - ζ.1 ^ a) := by ring
      rw [e]; exact this.neg
  · intro ζ x hx
    have h := congrArg (eval x) (prod_range ζ)
    simpa [eval_prod, hx] using h
  · intro ζ ξ
    have h := congrArg (eval ξ.1) (prod_coprime ζ)
    rw [← aeval_cyc, ξ.2.2] at h
    simpa [eval_prod] using h
  · intro r hr ζ
    have hq0 : q ≠ 0 := NeZero.ne q
    have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (Nat.eq_zero_of_zero_dvd hr)
    have hk0 : q / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hr) (Nat.pos_of_ne_zero hr0)).ne'
    have hunit : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have : IsUnit ((r : A) * k) := by rw [← Nat.cast_mul, ← hk]; exact ζ.2.1
      exact isUnit_of_mul_isUnit_left this
    have h : aeval (ζ.1 ^ (q / r)) (cyclotomic r ℤ) = 0 := by
      rw [← aeval_X_pow (R := ℤ), ← aeval_comp]
      apply transfer ζ
      rw [aeval_comp, aeval_X_pow, aeval_cyc]
      have hp := (μc_prim q).pow_of_dvd hk0 (Nat.div_dvd_of_dvd hr)
      rw [Nat.div_div_self hr hq0] at hp
      exact hp.isRoot_cyclotomic (Nat.pos_of_ne_zero hr0)
    exact ⟨(⟨ζ.1 ^ (q / r), hunit, h⟩ : {z : A // IsUnit (r : A) ∧ aeval z (cyclotomic r ℤ) = 0}), rfl⟩

end GlobalTheory.EtC.PrimBasic
