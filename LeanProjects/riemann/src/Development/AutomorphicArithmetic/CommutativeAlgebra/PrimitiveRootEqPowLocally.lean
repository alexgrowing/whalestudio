import Mathlib
import Development.EtaleCohomology.EtaleSheaves.DerivUnit

open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.primitive_root_eq_pow_locally :
    ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ξ ζ : Prim q A) (p : Ideal A) [p.IsPrime], ∃ (f : A) (a : (ZMod q)ˣ), f ∉ p ∧ ∀ (B : Type) [CommRing B] (φ : A →+* B), IsUnit (φ f) → φ ξ.1 = (φ ζ.1) ^ (a : ZMod q).val := by
  intro q _ A _ ξ ζ p _
  have hpow : ∀ η : Prim q A, η.1 ^ q = 1 := by
    intro η
    obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have h1 := congrArg (Polynomial.aeval η.1) hg
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, η.2.2, zero_mul] at h1
    exact sub_eq_zero.mp h1
  have hq' : IsUnit ((q : ℕ) : A ⧸ p) := by
    simpa using ζ.2.1.map (Ideal.Quotient.mk p)
  haveI : NeZero ((q : ℕ) : A ⧸ p) := ⟨hq'.ne_zero⟩
  have prim : ∀ η : Prim q A, IsPrimitiveRoot (Ideal.Quotient.mk p η.1) q := by
    intro η
    have h0 : Ideal.Quotient.mk p (Polynomial.aeval η.1 (Polynomial.cyclotomic q ℤ)) = 0 := by
      rw [η.2.2, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot,
      Polynomial.eval_map]
    have e : (Ideal.Quotient.mk p).comp (algebraMap ℤ A) = Int.castRingHom (A ⧸ p) :=
      RingHom.ext_int _ _
    rw [e] at h0
    exact h0
  obtain ⟨k, hk, hkξ⟩ := (prim ζ).eq_pow_of_pow_eq_one (prim ξ).pow_eq_one
  have hcop : k.Coprime q := ((prim ζ).pow_iff_coprime (NeZero.pos q) k).1 (hkξ ▸ prim ξ)
  have hcq : (ζ.1 ^ k) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow ζ, one_pow]
  have hf : (∑ i ∈ Finset.range q, ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i)) * (ξ.1 - ζ.1 ^ k) = 0 := by
    rw [geom_sum₂_mul, hpow ξ, hcq, sub_self]
  refine ⟨∑ i ∈ Finset.range q, ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i), ZMod.unitOfCoprime k hcop, ?_, ?_⟩
  · intro hmem
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hc : Ideal.Quotient.mk p (ζ.1 ^ k) = Ideal.Quotient.mk p ξ.1 := by
      rw [map_pow, hkξ]
    have hcu : IsUnit (Ideal.Quotient.mk p ξ.1) := by
      refine (Units.ofPowEqOne _ q ?_ (NeZero.ne q)).isUnit
      rw [← map_pow, hpow ξ, map_one]
    rw [map_sum] at hz
    have hsum : ∑ i ∈ Finset.range q, Ideal.Quotient.mk p (ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i)) =
        ∑ i ∈ Finset.range q, (Ideal.Quotient.mk p ξ.1) ^ (q - 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [map_mul, map_pow, map_pow, hc, ← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hz
    exact (hq'.mul (hcu.pow _)).ne_zero hz
  · intro B _ φ hφ
    have h1 := congrArg φ hf
    rw [map_mul, map_zero, hφ.mul_right_eq_zero, map_sub, sub_eq_zero] at h1
    rw [h1, map_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
