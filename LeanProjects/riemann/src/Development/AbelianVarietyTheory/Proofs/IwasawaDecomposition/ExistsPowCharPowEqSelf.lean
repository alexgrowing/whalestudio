import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrobTeich

variable {Ω : Type} [Field Ω]

theorem eq_of_pow_eq_self_of_cong (A : ValuationSubring Ω) {N : ℕ} (hN : A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = a) (hb : b ^ N = b) (hab : A.valuation (a - b) < 1) : a = b := by
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  · interval_cases N
    · rw [pow_zero] at ha hb; rw [← ha, ← hb]
    · simp at hN
  have hle : ∀ c : Ω, c ^ N = c → A.valuation c ≤ 1 := by
    intro c hc
    by_contra hc1
    have h1 : 1 < A.valuation c := not_le.mp hc1
    have h2 : A.valuation c ^ 1 < A.valuation c ^ N := pow_lt_pow_right₀ h1 (by omega)
    rw [← map_pow, ← map_pow, hc, pow_one] at h2
    exact lt_irrefl _ h2
  have ha1 := hle a ha
  have hb1 := hle b hb
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  set S := ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i) with hS
  have hS1 : S = 1 := by
    have h1 : S * (a - b) = a - b := by rw [hS, geom_sum₂_mul, ha, hb]
    have h2 : (S - 1) * (a - b) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hsub
  have hdiff : A.valuation (S - ∑ i ∈ Finset.range N, a ^ i * a ^ (N - 1 - i)) < 1 := by
    rw [hS, ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [← mul_sub, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (GlobalTheory.WeilDeligne.val_pow_le_one ha1 i))
      (GlobalTheory.WeilDeligne.cong_pow hb1 ha1 (GlobalTheory.WeilDeligne.cong_symm hab) _)
  rw [geom_sum₂_self] at hdiff
  have hNa : A.valuation ((N : Ω) * a ^ (N - 1)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (GlobalTheory.WeilDeligne.val_pow_le_one ha1 _)) hN
  have hS' : A.valuation S < 1 := by
    have e : S = (S - (N : Ω) * a ^ (N - 1)) + (N : Ω) * a ^ (N - 1) := by ring
    rw [e]; exact Valuation.map_add_lt _ hdiff hNa
  rw [hS1, map_one] at hS'
  exact lt_irrefl _ hS'

open Polynomial in

theorem exists_pow_eq_self_cong [IsAlgClosed Ω] (A : ValuationSubring Ω) {N : ℕ} (hN : 2 ≤ N)
    {x : Ω} (hx : A.valuation (x ^ N - x) < 1) : ∃ ζ : Ω, ζ ^ N = ζ ∧ A.valuation (x - ζ) < 1 := by
  set P : Polynomial Ω := X ^ N - X with hP
  have hdeg : P.natDegree = N := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
  have hmon : P.Monic := by
    rw [hP]; exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < N))
  have hsplit : P = (P.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [IsAlgClosed.card_roots_eq_natDegree])).symm
  have hev : x ^ N - x = (P.roots.map fun a => x - a).prod := by
    have := congrArg (eval x) hsplit
    rw [eval_multiset_prod, Multiset.map_map] at this
    simpa [hP, Function.comp_def] using this
  by_contra hno
  push_neg at hno
  have hge : ∀ a ∈ P.roots, 1 ≤ A.valuation (x - a) := by
    intro a ha
    refine hno a ?_
    have := (mem_roots hmon.ne_zero).mp ha
    simpa [hP, sub_eq_zero] using this
  have h1 : 1 ≤ A.valuation (x ^ N - x) := by
    rw [hev, map_multiset_prod]
    refine Multiset.prod_induction (fun c => 1 ≤ c) _ (fun a b ha hb => ?_) le_rfl ?_
    · simpa using mul_le_mul' ha hb
    · intro c hc
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hc
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
      exact hge a ha
  exact absurd hx (not_lt.mpr h1)

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

theorem exists_prime_pow_normV (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) : ∃ p f : ℕ, p.Prime ∧ 0 < f ∧ normV w = p ^ f ∧ A.valuation (p : Ω) < 1 := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  set p := ringChar (𝓞 E ⧸ w.asIdeal) with hp_def
  obtain ⟨n, hp, hn⟩ := FiniteField.card (𝓞 E ⧸ w.asIdeal) p
  have hpw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  refine ⟨p, n, hp, n.pos, ?_, ?_⟩
  · show Nat.card (𝓞 E ⧸ w.asIdeal) = p ^ (n : ℕ)
    rw [Nat.card_eq_fintype_card, hn]
  · have := (h _).mpr hpw
    simpa using this

theorem exists_pow_char_pow_eq_self {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (P : Polynomial ℤ) (hP : P.map (Int.castRingHom k) ≠ 0) {y : k}
    (hy : P.eval₂ (Int.castRingHom k) y = 0) : ∃ r : ℕ, 0 < r ∧ y ^ p ^ r = y := by
  have hroot : ∀ i : ℕ, y ^ p ^ i ∈ {z : k | (P.map (Int.castRingHom k)).IsRoot z} := by
    intro i
    show (P.map (Int.castRingHom k)).eval (y ^ p ^ i) = 0
    rw [Polynomial.eval_map, ← iterateFrobenius_def (R := k) p i,
      ← RingHom.ext_int ((iterateFrobenius k p i).comp (Int.castRingHom k)) (Int.castRingHom k),
      ← Polynomial.hom_eval₂, hy, map_zero]
  obtain ⟨i, j, hij, heq⟩ := (Polynomial.finite_setOf_isRoot hP).exists_lt_map_eq_of_forall_mem hroot
  refine ⟨j - i, by omega, ?_⟩
  apply (iterateFrobenius k p i).injective
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
  exact heq.symm

theorem exists_pow_prime_pow_cong [CharZero Ω] (A : ValuationSubring Ω) {x : Ω}
    (halg : IsAlgebraic ℤ x) (hx : A.valuation x ≤ 1) {p : ℕ} (hp : p.Prime)
    (hpA : A.valuation (p : Ω) < 1) : ∃ r : ℕ, 0 < r ∧ A.valuation (x ^ p ^ r - x) < 1 := by
  obtain ⟨P, hP0, hPx⟩ := halg
  set Q := P.primPart with hQ
  have hQprim : Q.IsPrimitive := P.isPrimitive_primPart
  have hQx : Polynomial.aeval x Q = 0 := by
    have e := congrArg (Polynomial.aeval x) P.eq_C_content_mul_primPart
    rw [hPx, map_mul, Polynomial.aeval_C] at e
    have hc : (algebraMap ℤ Ω) P.content ≠ 0 := by
      rw [eq_intCast, Int.cast_ne_zero]; exact (Polynomial.content_eq_zero_iff.not).mpr hP0
    exact (mul_eq_zero.mp e.symm).resolve_left hc
  haveI : Fact p.Prime := ⟨hp⟩
  set k := IsLocalRing.ResidueField A
  set y : A := ⟨x, (A.valuation_le_one_iff x).mp hx⟩ with hy_def
  haveI : CharP k p := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    simpa using hpA
  have hmap : Q.map (Int.castRingHom k) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ Q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun g => Polynomial.coeff g i) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
      exact (CharP.intCast_eq_zero_iff k p _).mp this
    have hu := hQprim (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    rcases hu with hu | hu <;> omega
  have hyA : Q.eval₂ (Int.castRingHom A) y = 0 := by
    apply Subtype.ext
    have e := Polynomial.hom_eval₂ Q (Int.castRingHom A) A.subtype y
    rw [RingHom.ext_int (A.subtype.comp (Int.castRingHom A)) (algebraMap ℤ Ω)] at e
    change A.subtype _ = A.subtype 0
    rw [e, map_zero]; exact hQx
  have hyk : Q.eval₂ (Int.castRingHom k) (IsLocalRing.residue A y) = 0 := by
    rw [← RingHom.ext_int ((IsLocalRing.residue A).comp (Int.castRingHom A)) (Int.castRingHom k),
      ← Polynomial.hom_eval₂, hyA, map_zero]
  obtain ⟨r, hr, hyr⟩ := exists_pow_char_pow_eq_self p Q hmap hyk
  refine ⟨r, hr, ?_⟩
  have hmem : y ^ p ^ r - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hyr, sub_self]
  have := (A.valuation_lt_one_iff _).mp hmem
  simpa [hy_def] using this

theorem exists_pow_normV_pow_cong [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ A.valuation (x ^ normV w ^ m - x) < 1 := by
  obtain ⟨p, f, hp, hf, hq, hpA⟩ := exists_prime_pow_normV A w h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨r, hr, hxr⟩ := exists_pow_prime_pow_cong A halg hx hp hpA
  refine ⟨r, hr, ?_⟩
  have key : ∀ j : ℕ, A.valuation (x ^ (p ^ r) ^ j - x) < 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := GlobalTheory.WeilDeligne.cong_pow (GlobalTheory.WeilDeligne.val_pow_le_one hx _) hx ih (p ^ r)
      rw [← pow_mul, ← pow_succ] at h1
      exact GlobalTheory.WeilDeligne.cong_trans h1 hxr
  have e : normV w ^ r = (p ^ r) ^ f := by rw [hq, ← pow_mul, ← pow_mul, mul_comm]
  rw [e]; exact key f

end GlobalTheory.FrobTeich

open GlobalTheory.FrobTeich in
theorem GlobalTheory.FrobTeich.isFrob_iff_teichmuller : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (σ : G E Ω), IsFrob (F := E) A (normV w) σ ↔ σ ∈ Dec (F := E) A ∧ ∀ (ζ : Ω) (m : ℕ), 0 < m → ζ ^ normV w ^ m = ζ → σ ζ = ζ ^ normV w := by
  intro E Ω _ _ _ _ _ A w h σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨p, f, hp, hf, hq, hpA⟩ := exists_prime_pow_normV A w h
  set q := normV w with hq_def
  have hqA : A.valuation (q : Ω) < 1 := by
    rw [hq, Nat.cast_pow, map_pow]; exact pow_lt_one₀ zero_le hpA hf.ne'
  have hq2 : 2 ≤ q := by rw [hq]; exact le_trans hp.two_le (Nat.le_self_pow hf.ne' p)
  constructor
  · rintro ⟨hD, hc⟩
    refine ⟨hD, fun ζ m hm hζ => ?_⟩
    have hNA : A.valuation ((q ^ m : ℕ) : Ω) < 1 := by
      rw [Nat.cast_pow, map_pow]; exact pow_lt_one₀ zero_le hqA hm.ne'
    have hζ1 : A.valuation ζ ≤ 1 := by
      by_contra hc1
      have h1 : 1 < A.valuation ζ := not_le.mp hc1
      have h2 : A.valuation ζ ^ 1 < A.valuation ζ ^ (q ^ m) :=
        pow_lt_pow_right₀ h1 (Nat.one_lt_pow hm.ne' (by omega))
      rw [← map_pow, ← map_pow, hζ, pow_one] at h2
      exact lt_irrefl _ h2
    refine eq_of_pow_eq_self_of_cong A hNA ?_ ?_ (hc ζ hζ1)
    · rw [← map_pow, hζ]
    · rw [← pow_mul, mul_comm, pow_mul, hζ]
  · rintro ⟨hD, hT⟩
    refine ⟨hD, fun x hx => ?_⟩
    obtain ⟨m, hm, hxm⟩ := exists_pow_normV_pow_cong A w h hx
    obtain ⟨ζ, hζ, hxζ⟩ := exists_pow_eq_self_cong A
      (le_trans hq2 (Nat.le_self_pow hm.ne' q)) hxm
    have hσζ := hT ζ m hm hζ
    have hζ1 : A.valuation ζ ≤ 1 := by
      have e : ζ = x - (x - ζ) := by ring
      rw [e]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hx hxζ.le)
    have e : σ x - x ^ q = σ (x - ζ) + (ζ ^ q - x ^ q) := by
      rw [map_sub, hσζ]; ring
    rw [e]
    refine Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hD _).mpr hxζ) ?_
    exact GlobalTheory.WeilDeligne.cong_pow hζ1 hx (GlobalTheory.WeilDeligne.cong_symm hxζ) q
