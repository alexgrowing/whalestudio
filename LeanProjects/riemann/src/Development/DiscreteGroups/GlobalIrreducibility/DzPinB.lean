import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzPinA
import Development.DiscreteGroups.GlobalIrreducibility.DzStickTeich

noncomputable section

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain Polynomial

namespace DiscreteGroups.sglob.DzPin

theorem exists_maximal_above (L : Type) [Field L] [NumberField L] (p : ℕ) [hp : Fact p.Prime] :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ (p : 𝓞 L) ∈ Q := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 L)) ≤ Ideal.span {(p : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 L)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) _ hker
  refine ⟨Q, hQ, ?_⟩
  have h : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 L)) Q := hQc ▸ Ideal.subset_span rfl
  simpa using h

theorem exists_iota (L : Type) [Field L] [NumberField L] (p : ℕ) [hp : Fact p.Prime]
    (Q : Ideal (𝓞 L)) [hQ : Q.IsMaximal] (hpQ : (p : 𝓞 L) ∈ Q) {N : ℕ} {μ : 𝓞 L}
    (hμ : IsPrimitiveRoot μ N) (hNQ : (N : 𝓞 L) ∉ Q) (K : Type) [Field K] [Fintype K]
    [Algebra (ZMod p) K] (hK : Fintype.card K = N + 1) : Nonempty (K →+* 𝓞 L ⧸ Q) := by
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  have hpz : ((p : ℕ) : 𝓞 L ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    exact hpQ
  haveI : CharP (𝓞 L ⧸ Q) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpz)
  letI : Algebra (ZMod p) (𝓞 L ⧸ Q) := ZMod.algebra _ p
  haveI := FiniteField.isSplittingField_sub K (ZMod p)
  have hμ' : IsPrimitiveRoot (Ideal.Quotient.mk Q μ) N := Stick.isPrimitiveRoot_mk Q hNQ hμ
  have hs : (map (algebraMap (ZMod p) (𝓞 L ⧸ Q)) (X ^ Fintype.card K - X)).Splits := by
    have e : (X ^ Fintype.card K - X : (𝓞 L ⧸ Q)[X]) = X * (X ^ N - C 1) := by
      rw [hK, C_1]; ring
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, e]
    exact Splits.X.mul (X_pow_sub_one_splits hμ')
  exact ⟨(IsSplittingField.lift K (X ^ Fintype.card K - X) hs).toRingHom⟩

theorem exists_emb (m : ℕ) [NeZero m] (L : Type) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {m} ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) (c : ℂ)
    (hc : IsPrimitiveRoot c m) : ∃ φ : L →+* ℂ, φ ζ = c := by
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos m)
  let x : primitiveRoots m ℂ := ⟨c, (mem_primitiveRoots (NeZero.pos m)).2 hc⟩
  refine ⟨((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm x).toRingHom, ?_⟩
  have h := congrArg Subtype.val ((hζ.embeddingsEquivPrimitiveRoots ℂ hirr).apply_symm_apply x)
  rw [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe] at h
  exact h

theorem exists_setup (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K]
    [Fintype K] [Algebra (ZMod p) K] (hK : Fintype.card K = p ^ n) (ψ₀ : AddChar (ZMod p) Circle)
    (hψ₀ : ψ₀ ≠ 1) :
    ∃ (Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ)))
      (ω : MulChar K (𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ))) (Ω : Kˣ →* ℂˣ),
      Function.Injective Ω ∧
      ∀ t : ℕ, t.Coprime (p * (p ^ n - 1)) →
        ∃ (Φ : 𝓞 (CyclotomicField (p * (p ^ n - 1)) ℚ) →+* ℂ) (D : Stick.GSDatum p n K _ Q),
          Function.Injective Φ ∧ D.ω = ω ∧ Φ D.ζ = ((ψ₀ 1 : Circle) : ℂ) ∧
          ∀ z : Kˣ, Φ (ω z) = ((Ω z : ℂˣ) : ℂ) ^ t := by
  classical
  have hp2 := hp.out.two_le
  have hpn : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  set N := p ^ n - 1 with hNdef
  have hN1 : N + 1 = p ^ n := by omega
  have hN0 : 0 < N := by omega
  haveI : NeZero N := ⟨by omega⟩
  haveI : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.out.ne_zero (by omega)⟩
  haveI : NeZero (((p * N : ℕ)) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  haveI : IsCyclotomicExtension {p * N} ℚ (CyclotomicField (p * N) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (p * N) ℚ
    all_goals rfl
  have hζL := IsCyclotomicExtension.zeta_spec (p * N) ℚ (CyclotomicField (p * N) ℚ)
  let z : 𝓞 (CyclotomicField (p * N) ℚ) := hζL.toInteger
  have hzL : algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ) z = IsCyclotomicExtension.zeta (p * N) ℚ (CyclotomicField (p * N) ℚ) := rfl
  have hz : IsPrimitiveRoot z (p * N) := hζL.toInteger_isPrimitiveRoot
  have hμ : IsPrimitiveRoot (z ^ p) N := hz.pow (NeZero.pos _) rfl
  obtain ⟨Q0, hQmax, hpQ⟩ := exists_maximal_above (CyclotomicField (p * N) ℚ) p
  have hNQ : (N : 𝓞 (CyclotomicField (p * N) ℚ)) ∉ Q0 := by
    intro h
    have h1 : (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n ∈ Q0 := Ideal.pow_mem_of_mem _ hpQ n (by omega)
    have h2 : (1 : 𝓞 (CyclotomicField (p * N) ℚ)) = (p : 𝓞 (CyclotomicField (p * N) ℚ)) ^ n - N := by
      have e : ((N + 1 : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) = ((p ^ n : ℕ) : 𝓞 (CyclotomicField (p * N) ℚ)) := by rw [hN1]
      push_cast at e
      rw [← e]; ring
    exact hQmax.ne_top ((Ideal.eq_top_iff_one _).2 (h2 ▸ Q0.sub_mem h1 h))
  obtain ⟨ι⟩ := exists_iota (CyclotomicField (p * N) ℚ) p Q0 hpQ hμ hNQ K (by omega)
  have hne : Q0 ≠ ⊥ := by
    rintro rfl
    exact (Nat.cast_ne_zero.mpr hp.out.ne_zero) ((Submodule.mem_bot _).1 hpQ)
  let Q : HeightOneSpectrum (𝓞 (CyclotomicField (p * N) ℚ)) := ⟨Q0, hQmax.isPrime, hne⟩
  obtain ⟨ω, hω1, hωN⟩ := Stick.exists_powResChar Q0 ι (n := N) (by rw [hK]) hμ
  have hdiv : (Fintype.card K - 1) / N = 1 := by rw [hK, ← hNdef, Nat.div_self hN0]
  have mk_ω : ∀ x, Ideal.Quotient.mk Q.asIdeal (ω x) = ι x := by
    intro x
    have h := hω1 x
    rw [hdiv, pow_one] at h
    exact h
  have hωu : ∀ y : Kˣ, ω y ^ N = 1 := by
    intro y; rw [← MulChar.pow_apply_coe, hωN, MulChar.one_apply_coe]

  let c : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p * N : ℕ) : ℂ))
  have hc : IsPrimitiveRoot c (p * N) := Complex.isPrimitiveRoot_exp _ (NeZero.ne _)
  have hemb : ∀ t : ℕ, t.Coprime (p * N) →
      ∃ Φ : 𝓞 (CyclotomicField (p * N) ℚ) →+* ℂ, Function.Injective Φ ∧ Φ z = c ^ t := by
    intro t ht
    obtain ⟨φ, hφ⟩ := exists_emb (p * N) (CyclotomicField (p * N) ℚ) hζL (c ^ t) (hc.pow_of_coprime t ht)
    exact ⟨φ.comp (algebraMap (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)), φ.injective.comp (IsFractionRing.injective (𝓞 (CyclotomicField (p * N) ℚ)) (CyclotomicField (p * N) ℚ)),
      by rw [RingHom.comp_apply, hzL, hφ]⟩
  obtain ⟨Φ1, hΦ1i, hΦ1z⟩ := hemb 1 (Nat.coprime_one_left _)

  let Ω : Kˣ →* ℂˣ := (Units.map Φ1.toMonoidHom).comp ω.toUnitHom
  have hΩ : ∀ y : Kˣ, ((Ω y : ℂˣ) : ℂ) = Φ1 (ω y) := fun y => rfl
  refine ⟨Q, ω, Ω, ?_, ?_⟩
  · intro y₁ y₂ h
    have h1 : Φ1 (ω y₁) = Φ1 (ω y₂) := by rw [← hΩ, ← hΩ, h]
    have h2 := congrArg (Ideal.Quotient.mk Q.asIdeal) (hΦ1i h1)
    rw [mk_ω, mk_ω] at h2
    exact Units.ext (ι.injective h2)
  · intro t ht
    obtain ⟨Φ, hΦi, hΦz⟩ := hemb t ht

    have hpow : ∀ x : 𝓞 (CyclotomicField (p * N) ℚ), x ^ N = 1 → Φ x = Φ1 x ^ t := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hx
      simp only [map_pow, hΦz, hΦ1z, pow_one]
      ring

    have hw : IsPrimitiveRoot ((ψ₀ 1 : Circle) : ℂ) p := by
      have h1 : ((ψ₀ 1 : Circle) : ℂ) ^ p = 1 := by
        rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_one, ZMod.natCast_self,
          AddChar.map_zero_eq_one, Circle.coe_one]
      have h2 : ((ψ₀ 1 : Circle) : ℂ) ≠ 1 := by
        intro h
        apply hψ₀
        refine AddChar.ext_iff.2 fun y => Circle.coe_injective ?_
        rw [addChar_apply_eq_pow, h, one_pow, AddChar.one_apply, Circle.coe_one]
      have h3 := IsPrimitiveRoot.orderOf ((ψ₀ 1 : Circle) : ℂ)
      rwa [orderOf_eq_prime h1 h2] at h3
    have hzN : IsPrimitiveRoot (Φ (z ^ N)) p := by
      rw [map_pow, hΦz]
      exact (hc.pow_of_coprime t ht).pow (NeZero.pos _) (by ring)
    obtain ⟨j, -, hj⟩ := hzN.eq_pow_of_pow_eq_one hw.pow_eq_one
    have hΦζ : Φ ((z ^ N) ^ j) = ((ψ₀ 1 : Circle) : ℂ) := by rw [map_pow, hj]
    have hprim : IsPrimitiveRoot ((z ^ N) ^ j) p :=
      IsPrimitiveRoot.of_map_of_injective (f := Φ) (by rw [hΦζ]; exact hw) hΦi
    let D : Stick.GSDatum p n K (𝓞 (CyclotomicField (p * N) ℚ)) Q :=
      { card_eq := hK, ι := ι, ω := ω, mk_ω := mk_ω, ζ := (z ^ N) ^ j, prim := hprim }
    refine ⟨Φ, D, hΦi, rfl, hΦζ, fun y => ?_⟩
    rw [hpow _ (hωu y), hΩ]

theorem nm_eq {g : ℕ} [hg : Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Fintype K]
    [Algebra (ZMod g) K] (hK : Fintype.card K = g ^ n) (Ω : Kˣ →* ℂˣ) (m : ℕ) :
    ((Ω.comp (Units.map (algebraMap (ZMod g) K).toMonoidHom)) ^ m).comp
        (Units.map (Algebra.norm (ZMod g) : K →* ZMod g)) = Ω ^ ((g ^ n - 1) / (g - 1) * m) := by
  have hg2 := hg.out.two_le
  have hfin : Module.finrank (ZMod g) K = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hK] at h
    exact (Nat.pow_right_injective hg2 h).symm
  refine MonoidHom.ext fun z => ?_
  have hz : Units.map (algebraMap (ZMod g) K).toMonoidHom
      (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z) = z ^ ((g ^ n - 1) / (g - 1)) := by
    refine Units.ext ?_
    simp only [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe]
    rw [FiniteField.algebraMap_norm_eq_prod_pow, Finset.prod_pow_eq_pow_sum, Nat.card_zmod, hfin,
      Nat.geomSum_eq hg2]
  rw [MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, hz, map_pow, ← pow_mul,
    MonoidHom.pow_apply]

end DiscreteGroups.sglob.DzPin
