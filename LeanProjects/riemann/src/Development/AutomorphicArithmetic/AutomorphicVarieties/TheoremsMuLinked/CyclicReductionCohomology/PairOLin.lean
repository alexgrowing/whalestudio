import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem pairO_lin (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (φ : ℤ_[l] →+* R) (k : ℕ)
    (hk : ∀ x : R, l ^ k • x = 0) (τ : R →+ ZMod (l ^ k)) (a : ℤ_[l]) (x : R) :
    τ (φ a * x) = PadicInt.toZModPow k a * τ x := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set n : ℕ := (PadicInt.toZModPow k a).val with hn
  have h1 : a - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hn, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨b, hb⟩ := h1
  have h2 : a = (n : ℤ_[l]) + (l : ℤ_[l]) ^ k * b := by rw [← hb]; ring
  have h3 : φ a * x = n • x := by
    have := hk (φ b * x)
    rw [nsmul_eq_mul, Nat.cast_pow] at this
    rw [h2, map_add, map_mul, map_pow, map_natCast, map_natCast, add_mul, mul_assoc, this, add_zero, nsmul_eq_mul]
  rw [h3, map_nsmul, nsmul_eq_mul, hn, ZMod.natCast_zmod_val]

private theorem pairO_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : Irreducible t)
    (m : ℕ) (x : Om O (m + 1)) (hx : x ≠ 0) : ∃ z, x * z = Ideal.Quotient.mk _ (t ^ m) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy ht
  have hn : n ≤ m := by
    by_contra h
    apply hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_left (pow_dvd_pow t (by omega)) _
  refine ⟨Ideal.Quotient.mk _ ((u⁻¹ : Oˣ) * t ^ (m - n)), ?_⟩
  rw [← map_mul]
  congr 1
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add]
  congr 1
  omega

theorem UpperTheory.V.Th.pairO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (m : ℕ), ∃ (k : ℕ) (τ : Om O m →+ ZMod (l ^ k)), 0 < k ∧ (∀ x, (∀ z, τ (x * z) = 0) → x = 0) ∧ ∀ (a : ℤ_[l]) x, τ (algebraMap O (Om O m) (algebraMap ℤ_[l] O a) * x) = PadicInt.toZModPow k a * τ x := by
  intro l _ O _ _ _ _ _ m
  obtain ⟨hfin, -, hkill, -⟩ := (UpperTheory.V.Th.omFacts l O).2 m
  have hk : ∀ x : Om O m, l ^ (m + 1) • x = 0 := fun x => by
    rw [pow_succ, mul_smul, hkill]
  have main : ∃ τ : Om O m →+ ZMod (l ^ (m + 1)), ∀ x, (∀ z, τ (x * z) = 0) → x = 0 := by
    cases m with
    | zero =>
      refine ⟨0, fun x _ => ?_⟩
      simpa using hkill x
    | succ m =>
      obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible O
      haveI : NeZero (l ^ (m + 1 + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      letI : Module (ZMod (l ^ (m + 1 + 1))) (Om O (m + 1)) := AddCommGroup.zmodModule hk
      have h0 : (Ideal.Quotient.mk _ (t ^ m) : Om O (m + 1)) ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem, ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
          pow_dvd_pow_iff ht.ne_zero ht.not_isUnit]
        omega
      have h1 := (UpperTheory.V.Th.dualZ (l ^ (m + 1 + 1)) (Om O (m + 1))).2.1 (Ideal.Quotient.mk _ (t ^ m))
      obtain ⟨f, hf⟩ := not_forall.mp (mt h1 h0)
      refine ⟨f.toAddMonoidHom, fun x hx => ?_⟩
      by_contra hx0
      obtain ⟨z, hz⟩ := pairO_dvd O t ht m x hx0
      have := hx z
      rw [hz] at this
      exact hf this
  obtain ⟨τ, hτ⟩ := main
  exact ⟨m + 1, τ, Nat.succ_pos m, hτ, fun a x =>
    pairO_lin l (Om O m) ((algebraMap O (Om O m)).comp (algebraMap ℤ_[l] O)) (m + 1) hk τ a x⟩
