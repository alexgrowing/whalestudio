import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XJacPowNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XUniqConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsTer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.RedRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.JacDvd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem relNorm_ker (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (p : ℕ) [hp : Fact p.Prime] (π : 𝓞 K' →+* ZMod p) :
    Ideal.relNorm (𝓞 K) (RingHom.ker π) = RingHom.ker (π.comp (algebraMap (𝓞 K) (𝓞 K'))) := by
  obtain ⟨h1, -⟩ := (UpperTheory.V.Stick.red K' p (RingHom.ker π)).2 π rfl
  obtain ⟨h2, h3, -⟩ := (UpperTheory.V.Stick.red K p _).2 (π.comp (algebraMap (𝓞 K) (𝓞 K'))) rfl
  haveI : (RingHom.ker π).LiesOver (RingHom.ker (π.comp (algebraMap (𝓞 K) (𝓞 K')))) := ⟨by
    ext x; simp [Ideal.under, RingHom.mem_ker]⟩
  haveI := h3.isPrime
  obtain ⟨s, hs⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime (RingHom.ker π)
    (RingHom.ker (π.comp (algebraMap (𝓞 K) (𝓞 K'))))
  have h4 := Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') (RingHom.ker π)
  rw [hs, map_pow, h2, h1] at h4
  have : s = 1 := Nat.pow_right_injective hp.out.two_le (by simpa using h4)
  rw [hs, this, pow_one]

private theorem root_inj {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (N : ℕ)
    [NeZero N] (ζ : R) (hζ : IsPrimitiveRoot ζ N) (hπ : IsPrimitiveRoot (π ζ) N) (a b : R) (ha : a ^ N = 1)
    (hb : b ^ N = 1) (h : π a = π b) : a = b := by
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ha
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hb
  rw [map_pow, map_pow] at h
  rw [hπ.pow_inj hi hj h]

private theorem jac_cong {F R R' S : Type} [Field F] [Fintype F] [CommRing R] [CommRing R'] [CommRing S]
    (f : R →+* S) (g : R' →+* S) (χ : MulChar F R) (χ' : MulChar F R') (h : ∀ x, f (χ x) = g (χ' x)) (b : ℕ) :
    f (∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j)) = g (∏ j ∈ Finset.Ico 1 b, jacobiSum χ' (χ' ^ j)) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.1 hj).1; omega
  simp only [jacobiSum, map_sum, map_mul, MulChar.pow_apply' _ hj0, map_pow, h]

private theorem pow_cong {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] (q : ℕ) (hq : q.Prime)
    (hqP : (q : R) ∈ P) (a c : R) (h : a ^ q = c ^ q) : Ideal.Quotient.mk P a = Ideal.Quotient.mk P c := by
  haveI := Fact.mk hq
  haveI : CharP (R ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hqP)
  have : (Ideal.Quotient.mk P a - Ideal.Quotient.mk P c) ^ q = 0 := by
    rw [sub_pow_char, ← map_pow, ← map_pow, h, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 this)

private theorem jac_notMem {R : Type} [CommRing R] [IsDomain R] [CharZero R] (p : ℕ) [Fact p.Prime]
    (χ : MulChar (ZMod p) R) (b : ℕ) (hb : b < orderOf χ) (P : Ideal R) [hP : P.IsPrime] (hpP : (p : R) ∉ P) :
    (∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j)) ∉ P := by
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨j, hj, hm⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hj
  have hd := UpperTheory.V.Stick.jacDvd R p χ (χ ^ j)
    (by simpa using pow_ne_one_of_lt_orderOf (x := χ) (n := 1) one_ne_zero (by omega))
    (pow_ne_one_of_lt_orderOf (by omega) (by omega))
    (by rw [← pow_succ']; exact pow_ne_one_of_lt_orderOf (by omega) (by omega))
  exact hpP (Ideal.mem_of_dvd _ hd hm)

private theorem val_lt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a b c d : 𝓞 K) (ζ : K)
    (n : ℕ) (hn : n ≠ 0) (hζ : ζ ^ n = 1) (hb : b ∉ v.asIdeal)
    (h1 : Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal c)
    (h2 : Ideal.Quotient.mk v.asIdeal b = Ideal.Quotient.mk v.asIdeal d) :
    v.valuation K (ζ * ((a : K) / b) - ζ * ((c : K) / d)) < 1 := by
  have hd : d ∉ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hb ⊢; rwa [← h2]
  have hb0 : (b : K) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact zero_mem _)
  have hd0 : (d : K) ≠ 0 := fun h => hd (by rw [show d = 0 from Subtype.ext h]; exact zero_mem _)
  have hz : v.valuation K ζ = 1 := by
    have := congrArg (v.valuation K) hζ
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hn).1 this
  have vb : v.valuation K (b : K) = 1 := (v.valuation_eq_one_iff_notMem (K := K)).2 hb
  have vd : v.valuation K (d : K) = 1 := (v.valuation_eq_one_iff_notMem (K := K)).2 hd
  have hm : a * d - c * b ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, h1, h2, sub_self]
  have vm : v.valuation K ((a * d - c * b : 𝓞 K) : K) < 1 := (v.valuation_lt_one_iff_mem (K := K) _).2 hm
  have : ζ * ((a : K) / b) - ζ * ((c : K) / d) = ζ * ((a * d - c * b : 𝓞 K) : K) / (b * d) := by
    push_cast; field_simp
  rw [this, map_div₀, map_mul, map_mul, hz, vb, vd]
  simpa using vm

private theorem neg_mul_self (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
    (y : 𝓞 K) (hy : y ^ M = 1) : sgO M K (-1) y * y = 1 := by
  rw [sgO_apply M K _ hy, ← pow_succ]
  have : M ∣ (((-1 : (ZMod M)ˣ) : ZMod M)).val + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; simp
  obtain ⟨k, hk⟩ := this
  rw [hk, pow_mul, hy, one_pow]

private theorem inv_pow_q (M q : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
    (u : (ZMod M)ˣ) (hu : (u : ZMod M) = q) (y : 𝓞 K) (hy : y ^ M = 1) : ((sgO M K u).symm y) ^ q = y := by
  have : sgO M K u y = y ^ q := by
    rw [sgO_apply M K _ hy, hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hy]
  rw [← map_pow, ← this, RingEquiv.symm_apply_apply]

theorem UpperTheory.V.ML.xCongJac :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < M → ∀ (p : ℕ) [Fact p.Prime] (π : 𝓞 K' →+* ZMod p), p.Coprime (q * M) → ∀ (X' : K') (X : K),
    IsX (q * M) K' b (RingHom.ker π) X' → IsX M K b (Ideal.relNorm (𝓞 K) (RingHom.ker π)) X →
    ∃ ζ : K', ζ ^ (2 * (q * M)) = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → v.valuation K' (X' - ζ * algebraMap K K' ((sg M K u)⁻¹ X)) < 1 := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hb p hp π hcop X' X hX' hX
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hcM : p.Coprime M := Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hcop
  have hcq : p.Coprime q := Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hcop
  set ι := algebraMap (𝓞 K) (𝓞 K') with hι
  rw [relNorm_ker, ← hι] at hX
  have hz' := (IsCyclotomicExtension.zeta_spec (q * M) ℚ K').toInteger_isPrimitiveRoot
  have hz := (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨hπ', d, hd⟩ := UpperTheory.V.Stick.redRoot _ p π _ _ hcop hz'
  obtain ⟨hπ, -⟩ := UpperTheory.V.Stick.redRoot _ p (π.comp ι) _ _ hcM hz
  obtain ⟨χ', hχ', ho'⟩ := UpperTheory.V.Stick.teich _ p π _ d _ hz' hπ' hd.symm
  obtain ⟨χ, hχ, -⟩ := UpperTheory.V.Stick.teich _ p (π.comp ι) _ (d * q) _ hz hπ (by rw [hd]; ring)
  have e' : (p - 1) / (q * M) = d := by rw [hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne _))]
  have e : (p - 1) / M = d * q := by
    rw [hd, show q * M * d = M * (d * q) by ring, Nat.mul_div_cancel_left _ hM]
  have hbq : b < q * M := lt_of_lt_of_le hb (Nat.le_mul_of_pos_left _ hq.pos)
  have hJ' := UpperTheory.V.ML.xJac (q * M) K' b p π χ' hcop hbq (by rw [e']; exact hχ')
  have hJ := UpperTheory.V.ML.xJac M K b p (π.comp ι) χ hcM hb (by rw [e]; exact hχ)
  obtain ⟨-, -, k', hpk⟩ := (UpperTheory.V.Stick.red K' p (RingHom.ker π)).2 π rfl
  obtain ⟨-, -, k, -⟩ := (UpperTheory.V.Stick.red K p _).2 (π.comp ι) rfl
  obtain ⟨ζ', hζ', rfl⟩ := UpperTheory.V.ML.xUniq _ _ _ _ _ _ k'.ne_zero hJ' hX'
  obtain ⟨ζ, hζ, rfl⟩ := UpperTheory.V.ML.xUniq _ _ _ _ _ _ k.ne_zero hJ hX
  have key : ∀ x, x ≠ 0 → χ' x ^ q = ι (χ x) := fun x hx => by
    refine root_inj p π _ _ hz' hπ' _ _ ?_ ?_ ?_
    · rw [← pow_mul, mul_comm, pow_mul, (hχ' x hx).1, one_pow]
    · rw [← map_pow, mul_comm, pow_mul, (hχ x hx).1, one_pow, map_one]
    · rw [map_pow, (hχ' x hx).2, ← pow_mul]; exact (hχ x hx).2.symm
  set w : K' := algebraMap K K' ((sg M K u)⁻¹ ζ) with hw
  have hwp : w ^ (2 * (q * M)) = 1 := by
    rw [hw, ← map_pow, ← map_pow, show 2 * (q * M) = 2 * M * q by ring, pow_mul, hζ, one_pow, map_one, map_one]
  have hn : 2 * (q * M) ≠ 0 := mul_ne_zero two_ne_zero (NeZero.ne _)
  have hw0 : w ≠ 0 := by rintro h; rw [h, zero_pow hn] at hwp; exact zero_ne_one hwp
  refine ⟨ζ' / w, by rw [div_pow, hζ', hwp, div_one], fun v hv => ?_⟩
  haveI := v.isPrime
  have hpv : (p : 𝓞 K') ∉ v.asIdeal := fun h => by
    obtain ⟨a, c, hac⟩ := (Nat.isCoprime_iff_coprime.2 hcq).map (Int.castRingHom (𝓞 K'))
    simp only [eq_intCast, Int.cast_natCast] at hac
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hac ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hv)))
  set g : 𝓞 K →+* 𝓞 K' := ι.comp (sgO M K u).symm.toRingHom with hg
  have hgq : ∀ y : 𝓞 K, y ^ M = 1 → g y ^ q = ι y := fun y hy => by
    rw [hg, RingHom.comp_apply, ← map_pow]
    exact congrArg ι (inv_pow_q M q K u hu y hy)
  have c1 := jac_cong (Ideal.Quotient.mk v.asIdeal) ((Ideal.Quotient.mk v.asIdeal).comp g) χ' χ (fun x => by
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero]
    · exact pow_cong _ q hq hv _ _ (by rw [key x hx, hgq _ (hχ x hx).1])) b
  have c2 := jac_cong ((Ideal.Quotient.mk v.asIdeal).comp (sgO (q * M) K' (-1)).toRingHom)
    (((Ideal.Quotient.mk v.asIdeal).comp g).comp (sgO M K (-1)).toRingHom) χ' χ (fun x => by
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero]
    · refine pow_cong _ q hq hv (sgO (q * M) K' (-1) (χ' x)) (g (sgO M K (-1) (χ x))) ?_
      rw [hgq _ (by rw [← map_pow, (hχ x hx).1, map_one]), ← map_pow, key x hx]
      have h1 := neg_mul_self (q * M) K' (ι (χ x))
        (by rw [← map_pow, mul_comm, pow_mul, (hχ x hx).1, one_pow, map_one])
      have h2 := congrArg ι (neg_mul_self M K (χ x) (hχ x hx).1)
      rw [map_mul, map_one] at h2
      exact left_inv_eq_right_inv h1 (by rw [mul_comm]; exact h2)) b
  have hn' := jac_notMem p χ' b (ho'.symm ▸ hbq) v.asIdeal hpv
  generalize (∏ j ∈ Finset.Ico 1 b, jacobiSum χ' (χ' ^ j)) = J' at *
  generalize (∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j)) = J at *
  have hgc : ∀ y : 𝓞 K, ((g y : 𝓞 K') : K') = algebraMap K K' ((sg M K u)⁻¹ (y : K)) := fun y => rfl
  have := val_lt K' v (sgO (q * M) K' (-1) J') J' (g (sgO M K (-1) J)) (g J) ζ' _ hn hζ' hn' c2 c1
  rw [hgc, hgc] at this
  convert this using 3
  · rfl
  rw [map_mul, map_mul, ← hw, map_div₀, map_div₀, ← mul_assoc, div_mul_cancel₀ _ hw0]
  rfl
