import ReciprocityTheory.Chebotarev.SplitDef

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem liesOver_of_under_eq {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (P : Prm E') (q : Prm E) (hP : under P = q) : P.asIdeal.LiesOver q.asIdeal :=
  ⟨by rw [← hP, under_asIdeal]⟩

theorem prime_dvd_norm_sub_one_cyclotomic (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (P : Prm (CyclotomicField l E)) (hl : Nat.Coprime (Nrm P) l) : l ∣ Nrm P - 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have hz := (IsCyclotomicExtension.zeta_spec l E M).toInteger_isPrimitiveRoot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  have hq := hz.idealQuotient_mk (I := P.asIdeal) h1 hl
  have : P.asIdeal.IsMaximal := P.isMaximal
  let _ := Ideal.Quotient.field P.asIdeal
  have hu := hq.isUnit hlp.ne_zero
  have hu' : IsPrimitiveRoot hu.unit l := IsPrimitiveRoot.coe_units_iff.mp hq
  have hd : orderOf hu.unit ∣ Nat.card (𝓞 M ⧸ P.asIdeal)ˣ := orderOf_dvd_natCard _
  rw [← hu'.eq_orderOf, Nat.card_units] at hd
  simpa [Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hd

theorem norm_coprime_of_not_dvd_under (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) : Nat.Coprime (Nrm P) l := by
  have hlp : l.Prime := Fact.out
  have := liesOver_of_under_eq P q hP
  have hN : Nrm q ^ P.asIdeal.inertiaDeg (𝓞 E) = Nrm P :=
    Ideal.absNorm_pow_inertiaDeg q.asIdeal P.asIdeal
  have hcq : Nat.Coprime (Nrm q) l := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl)
  exact hN ▸ Nat.Coprime.pow_left _ hcq

theorem natCast_mem_of_not_coprime (E : Type) [Field E] [NumberField E] (n : ℕ) (q : Prm E)
    (h : ¬ Nat.Coprime (Nrm q) n) : ((n : ℕ) : 𝓞 E) ∈ q.asIdeal := by
  have : q.asIdeal.IsMaximal := q.isMaximal
  let _ := Ideal.Quotient.field q.asIdeal
  let _ : Fintype (𝓞 E ⧸ q.asIdeal) := Fintype.ofFinite _
  have := ringChar.charP (𝓞 E ⧸ q.asIdeal)
  obtain ⟨k, hcp, hcard⟩ := FiniteField.card (𝓞 E ⧸ q.asIdeal) (ringChar (𝓞 E ⧸ q.asIdeal))
  have hN : Nrm q = ringChar (𝓞 E ⧸ q.asIdeal) ^ (k : ℕ) := by
    rw [← hcard, Nrm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (𝓞 E ⧸ q.asIdeal) (ringChar (𝓞 E ⧸ q.asIdeal))]
  by_contra hd
  exact h (hN ▸ Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hcp).mpr hd))

theorem inertia_trivial_cyclotomic_coprime (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    [IsGalois E (CyclotomicField l E)]
    (P : Prm (CyclotomicField l E)) (hl : Nat.Coprime (Nrm P) l)
    (g : Gal(CyclotomicField l E/E)) (hg : g ∈ P.asIdeal.inertia Gal(CyclotomicField l E/E)) : g = 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have hz0 := IsCyclotomicExtension.zeta_spec l E M
  have hz := hz0.toInteger_isPrimitiveRoot
  set ζ := hz0.toInteger
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  have hq := hz.idealQuotient_mk (I := P.asIdeal) h1 hl
  have hgl : (g • ζ) ^ l = 1 := by rw [← smul_pow', hz.pow_eq_one, smul_one]
  obtain ⟨i, hi, hiz⟩ := hz.eq_pow_of_pow_eq_one hgl
  have hmem : g • ζ - ζ ∈ P.asIdeal := hg ζ
  rw [← hiz, ← Ideal.Quotient.eq, map_pow] at hmem
  have hi1 : i = 1 := hq.pow_inj hi hlp.one_lt (by rw [hmem, pow_one])
  rw [hi1, pow_one] at hiz
  have hfix : g (IsCyclotomicExtension.zeta l E M) = IsCyclotomicExtension.zeta l E M := by
    have := congrArg (fun x : 𝓞 M => (x : M)) hiz
    exact this.symm
  have hext : (g : M →ₐ[E] M) = AlgHom.id E M := by
    refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hz0) ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hfix
  ext x
  exact DFunLike.congr_fun hext x

theorem splitA_fibre (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (q : Prm E) :
    {P : Prm (CyclotomicField l E) | under P = q}.Finite ∧
      {P : Prm (CyclotomicField l E) | under P = q}.ncard ≤ l - 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have : IsGalois E M := IsCyclotomicExtension.isGalois {l} E M
  have hfin : (q.asIdeal.primesOver (𝓞 M)).Finite := Algebra.QuasiFinite.finite_primesOver q.asIdeal
  have hinj : Function.Injective (fun P : Prm M => P.asIdeal) := fun a b h =>
    IsDedekindDomain.HeightOneSpectrum.ext h
  have hmaps : ∀ P ∈ {P : Prm M | under P = q}, P.asIdeal ∈ q.asIdeal.primesOver (𝓞 M) := by
    intro P hP
    have := liesOver_of_under_eq P q hP
    exact ⟨P.isPrime, this⟩
  refine ⟨hfin.preimage hinj.injOn |>.subset hmaps, ?_⟩
  have h1 := Set.ncard_le_ncard_of_injOn _ hmaps hinj.injOn hfin
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn q.asIdeal (𝓞 M) Gal(M/E)
  have h3 : Nat.card Gal(M/E) = l - 1 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.finrank M hirr, Nat.totient_prime hlp]
  rw [h3] at h2
  have h4 : q.asIdeal.ramificationIdxIn (𝓞 M) * q.asIdeal.inertiaDegIn (𝓞 M) ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; have := hlp.two_le; omega
  have h5 := Nat.le_mul_of_pos_right ((q.asIdeal.primesOver (𝓞 M)).ncard) (Nat.pos_of_ne_zero h4)
  exact h1.trans (h5.trans h2.le)

theorem splitA_norm (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    (Nrm P = Nrm q ∧ ((Nrm q : ℕ) : ZMod l) = 1) ∨ Nrm q ^ 2 ≤ Nrm P := by
  have hlp : l.Prime := Fact.out
  have := liesOver_of_under_eq P q hP
  have hN : Nrm q ^ P.asIdeal.inertiaDeg (𝓞 E) = Nrm P :=
    Ideal.absNorm_pow_inertiaDeg q.asIdeal P.asIdeal
  have hf := Ideal.inertiaDeg_pos P.asIdeal (𝓞 E)
  have hcq : Nat.Coprime (Nrm q) l := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hlp).mpr hl)
  have hcP : Nat.Coprime (Nrm P) l := hN ▸ Nat.Coprime.pow_left _ hcq
  have hd := prime_dvd_norm_sub_one_cyclotomic E l P hcP
  have hq0 : Nrm q ≠ 0 := by
    intro h; exact hl (h ▸ dvd_zero l)
  rcases Nat.lt_or_ge (P.asIdeal.inertiaDeg (𝓞 E)) 2 with h2 | h2
  · have h1 : P.asIdeal.inertiaDeg (𝓞 E) = 1 := by omega
    rw [h1, pow_one] at hN
    refine Or.inl ⟨hN.symm, ?_⟩
    rw [← hN] at hd
    have h3 : ((Nrm q - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    have h4 : Nrm q = (Nrm q - 1) + 1 := by omega
    rw [h4, Nat.cast_add, h3, Nat.cast_one, zero_add]
  · exact Or.inr (hN ▸ Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq0) h2)

theorem splitA_finite_not_coprime (E : Type) [Field E] [NumberField E] (n : ℕ) (hn : n ≠ 0) :
    {q : Prm E | ¬ Nat.Coprime (Nrm q) n}.Finite := by
  have h0 : Ideal.span {((n : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun q hq => ?_
  exact (Ideal.dvd_span_singleton).mpr (natCast_mem_of_not_coprime E n q hq)

theorem splitA_unram (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    P.asIdeal.ramificationIdx (𝓞 E) = 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E (CyclotomicField l E)
  have := liesOver_of_under_eq P q hP
  have : q.asIdeal.IsMaximal := q.isMaximal
  have : Finite q.asIdeal.ResidueField :=
    Finite.of_surjective _ q.asIdeal.bijective_algebraMap_quotient_residueField.surjective
  have hcP := norm_coprime_of_not_dvd_under E l q P hP hl
  have hbot : P.asIdeal.inertia Gal(CyclotomicField l E/E) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun g hg => inertia_trivial_cyclotomic_coprime E l P hcP g hg
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal P.asIdeal Gal(CyclotomicField l E/E),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(CyclotomicField l E/E)) q.asIdeal P.asIdeal,
    hbot, Subgroup.card_bot]

end ReciprocityTheory.Cheb
