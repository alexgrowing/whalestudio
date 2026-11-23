import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import ReciprocityTheory.GaloisValuations.Global

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem natCast_mem_asIdeal_of_normV_eq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (p : ℕ)
    (hN : normV u = p) : ((p : 𝓞 F)) ∈ u.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hN]
  unfold Formalism.ConjugateSelfDual.normV
  simpa using card_nsmul_eq_zero' (G := 𝓞 F ⧸ u.asIdeal) (x := 1)

private theorem valuation_le_one_of_pow_eq_one' {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (y : Ω) (n : ℕ) (hn : 0 < n)
    (h : y ^ n = 1) : A.valuation y ≤ 1 := by
  have h1 : A.valuation y ^ n = 1 := by rw [← map_pow, h, map_one]
  exact (pow_le_one_iff hn.ne').mp h1.le

private theorem not_valuation_natCast_lt_one_of_prime_not_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p n : ℕ) (hp : Nat.Prime p)
    (hpn : ¬ p ∣ n) (hvp : A.valuation (p : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro hvn
  have hc : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  have hb : ((Nat.gcd p n : ℤ)) = p * Nat.gcdA p n + n * Nat.gcdB p n := Nat.gcd_eq_gcd_ab p n
  rw [hc.gcd_eq_one] at hb
  have hb' : (1 : Ω) = (p : Ω) * (Nat.gcdA p n : Ω) + (n : Ω) * (Nat.gcdB p n : Ω) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hb
  have hA : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have h1 : A.valuation ((p : Ω) * (Nat.gcdA p n : Ω)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hvp (hA _)
  have h2 : A.valuation ((n : Ω) * (Nat.gcdB p n : Ω)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hvn (hA _)
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hb', map_one] at h3
  exact lt_irrefl _ h3

open Polynomial in
private theorem exists_zmod_castHom_eq_of_pow_char_eq_self {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (z : K)
    (hz : z ^ p = z) : ∃ k : ZMod p, (ZMod.castHom (dvd_refl p) K) k = z := by
  set f := ZMod.castHom (dvd_refl p) K
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [hcard] at this
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]; exact_mod_cast hp.out.one_lt
  have hdeg : (X ^ p - X : (ZMod p)[X]).roots.card = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.out.one_lt]
    simp [hcard]
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hdeg
  have hev := congrArg (fun P => (P.map f).eval z) hprod
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, eval_sub, eval_X, eval_C,
    eval_pow, hz, sub_self] at hev
  obtain ⟨w, -, hw0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)
  exact ⟨w, (sub_eq_zero.mp hw0).symm⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.rootMod :
    RootMod := by
  intro F Ω _ _ _ _ _ A u hu p hp hN y n hn hfix
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hu
  have hfy : σ y = y := hfix σ hσD
  have hvp : A.valuation (p : Ω) < 1 := by
    have h := (hu (p : 𝓞 F)).mpr (natCast_mem_asIdeal_of_normV_eq u p hN)
    simpa using h
  refine ⟨fun m hm => ?_, fun hprim hpn => ?_⟩
  · have hvy : A.valuation y ≤ 1 := by
      have h1 : A.valuation y ^ n ≤ 1 := by
        rw [← map_pow, hm]; exact valuation_natCast_le_one A m
      exact (pow_le_one_iff hn.ne').mp h1
    have hyA : y ∈ A := (A.valuation_le_one_iff y).mp hvy
    set yA : A := ⟨y, hyA⟩
    set r := IsLocalRing.residue A
    have hp0 : ((p : IsLocalRing.ResidueField A)) = 0 := by
      rw [← map_natCast r, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      simpa using hvp
    have hch : ringChar (IsLocalRing.ResidueField A) = p :=
      (hp.eq_one_or_self_of_dvd _ (ringChar.dvd hp0)).resolve_left (CharP.ringChar_ne_one)
    haveI := ringChar.of_eq hch
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt := hσ y hvy
    rw [hfy, hN] at hlt
    have hry : r yA ^ p = r yA := by
      have h0 : r (yA - yA ^ p) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
        simpa using hlt
      rw [map_sub, map_pow, sub_eq_zero] at h0
      exact h0.symm
    obtain ⟨k, hk⟩ := exists_zmod_castHom_eq_of_pow_char_eq_self p (r yA) hry
    have hyn : yA ^ n = (m : A) := by
      apply Subtype.ext
      simpa using hm
    have hkm : (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (k ^ n) =
        (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) (m : ZMod p) := by
      rw [map_pow, hk, ← map_pow, hyn, map_natCast, map_natCast]
    exact ⟨k, (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)).injective hkm⟩
  · have hyn : y ^ n = 1 := hprim.pow_eq_one
    have hvy := valuation_le_one_of_pow_eq_one' A y n hn hyn
    have hlt := hσ y hvy
    rw [hfy, hN] at hlt
    have hvn := not_valuation_natCast_lt_one_of_prime_not_dvd A p n hp hpn hvp
    have hyp : y = y ^ p := by
      refine eq_of_pow_eq_one A hvn hyn ?_ hlt
      rw [← pow_mul, mul_comm, pow_mul, hyn, one_pow]
    have hy0 : y ≠ 0 := hprim.ne_zero hn.ne'
    have hp1 : y ^ (p - 1) = 1 := by
      have h2 : y ^ (p - 1) * y = 1 * y := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_le]
        exact hyp.symm
      exact mul_right_cancel₀ hy0 h2
    exact hprim.dvd_of_pow_eq_one _ hp1
