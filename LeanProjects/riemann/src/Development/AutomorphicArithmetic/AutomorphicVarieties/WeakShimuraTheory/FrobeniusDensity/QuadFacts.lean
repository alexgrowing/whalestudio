import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exists_conj (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) :
    ∃ t : K ≃ₐ[ℚ] K, t ≠ 1 ∧ (∀ s : K ≃ₐ[ℚ] K, s ≠ 1 → s = t) ∧
      ∀ x : 𝓞 K, x * RingOfIntegers.mapRingEquiv t.toRingEquiv x = ((Algebra.norm ℤ x : ℤ) : 𝓞 K) := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  have hc : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h]
  obtain ⟨t, ht⟩ : ∃ t : K ≃ₐ[ℚ] K, t ≠ 1 := by
    by_contra hne
    push_neg at hne
    have : Fintype.card (K ≃ₐ[ℚ] K) ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by
      rw [hne a, hne b]
    omega
  have huniq : ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 → s = t := by
    intro s hs
    by_contra hst
    classical
    have h3 : ({1, s, t} : Finset (K ≃ₐ[ℚ] K)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hst]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hs, Ne.symm ht⟩
    have := Finset.card_le_univ ({1, s, t} : Finset (K ≃ₐ[ℚ] K))
    omega
  refine ⟨t, ht, huniq, fun x => ?_⟩
  classical
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, t} := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hs : s = 1
    · exact Or.inl hs
    · exact Or.inr (huniq s hs)
  apply RingOfIntegers.ext
  have key := Algebra.norm_eq_prod_automorphisms ℚ (x : K)
  rw [huniv, Finset.prod_pair (Ne.symm ht)] at key
  simp only [map_mul, RingOfIntegers.mapRingEquiv_apply, map_intCast]
  rw [← Algebra.coe_norm_int] at key
  simp only [AlgEquiv.one_apply] at key
  change (x : K) * t (x : K) = _
  rw [← key]
  simp

private theorem mul_map {K : Type} [Field K] [NumberField K] (τ : 𝓞 K ≃+* 𝓞 K)
    (hτ : ∀ x : 𝓞 K, x * τ x = ((Algebra.norm ℤ x : ℤ) : 𝓞 K)) (I : Ideal (𝓞 K)) :
    I * I.map τ = Ideal.span {(Ideal.absNorm I : 𝓞 K)} := by
  classical
  have hspan : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} ≤ I * I.map τ := by
    have h1 : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.relNorm ℤ I) =
        Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} := by
      rw [Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]
      simp
    rw [← h1, Ideal.map_relNorm, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, Algebra.intNorm_eq_norm, eq_intCast]
    rw [← hτ x]
    exact Ideal.mul_mem_mul hx (Ideal.mem_map_of_mem _ hx)
  have hd : Module.finrank ℤ (𝓞 K) = 2 := by
    have h2 := hτ 2
    rw [map_ofNat, show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 by simp, Algebra.norm_algebraMap] at h2
    have h4 : ((4 : ℤ) : 𝓞 K) = ((2 ^ Module.finrank ℤ (𝓞 K) : ℤ) : 𝓞 K) := by
      rw [← h2]
      simp
      norm_num
    have h5 : (2 : ℤ) ^ Module.finrank ℤ (𝓞 K) = 2 ^ 2 := by
      have := Int.cast_injective (α := 𝓞 K) h4
      rw [← this]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h5)
  have hmap : Ideal.absNorm (I.map τ) = Ideal.absNorm I := by
    rw [← Ideal.absNorm_relNorm ℤ (𝓞 K) (I.map τ), ← Ideal.absNorm_relNorm ℤ (𝓞 K) I]
    congr 1
    exact Ideal.relNorm_map_algEquiv τ.toIntAlgEquiv I
  have habs : Ideal.absNorm (Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)}) =
      Ideal.absNorm I ^ 2 := by
    rw [Ideal.absNorm_span_singleton, show ((Ideal.absNorm I : ℕ) : 𝓞 K) =
      algebraMap ℤ (𝓞 K) (Ideal.absNorm I : ℤ) by simp, Algebra.norm_algebraMap, hd]
    simp [Int.natAbs_pow]
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hspan
  by_cases hn : Ideal.absNorm I = 0
  · rw [Ideal.absNorm_eq_zero_iff] at hn
    subst hn
    simp
  · have h3 := congrArg Ideal.absNorm hL
    rw [map_mul, map_mul, hmap, habs] at h3
    have hL1 : Ideal.absNorm L = 1 := by
      have hpos : 0 < Ideal.absNorm I * Ideal.absNorm I := Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hn)
      have : Ideal.absNorm I * Ideal.absNorm I * 1 = Ideal.absNorm I * Ideal.absNorm I * Ideal.absNorm L := by
        rw [mul_one, ← h3, sq]
      exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
    rw [Ideal.absNorm_eq_one_iff] at hL1
    rw [hL, hL1, Ideal.mul_top]

private theorem dvd_of_mem {K : Type} [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) {a b : ℕ}
    (hab : (b : 𝓞 K) ∈ Ideal.span {(a : 𝓞 K)}) : a ∣ b := by
  rw [Ideal.mem_span_singleton] at hab
  have hn := map_dvd (Algebra.norm ℤ) hab
  rw [show (a : 𝓞 K) = algebraMap ℤ (𝓞 K) (a : ℤ) by simp,
    show (b : 𝓞 K) = algebraMap ℤ (𝓞 K) (b : ℤ) by simp, Algebra.norm_algebraMap,
    Algebra.norm_algebraMap, RingOfIntegers.rank, h, Int.pow_dvd_pow_iff two_ne_zero] at hn
  exact_mod_cast hn

private theorem split_facts {K : Type} [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) (τ : 𝓞 K ≃+* 𝓞 K)
    (hτ : ∀ I : Ideal (𝓞 K), I * I.map τ = Ideal.span {(Ideal.absNorm I : 𝓞 K)}) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hne : w.asIdeal ≠ w.asIdeal.map τ) :
    Ideal.absNorm w.asIdeal = p ∧ IsCoprime w.asIdeal (w.asIdeal.map τ) ∧
      ∀ n : ℕ, ∃ φ : 𝓞 K →+* ZMod (p ^ n), RingHom.ker φ = w.asIdeal ^ n := by
  classical
  haveI hwm : w.asIdeal.IsMaximal := w.isMaximal
  haveI hτm : (w.asIdeal.map τ).IsMaximal := Ideal.map_isMaximal_of_equiv τ
  have hcop : IsCoprime w.asIdeal (w.asIdeal.map τ) :=
    Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne hwm hτm hne)
  have hpτ : (p : 𝓞 K) ∈ w.asIdeal.map τ := by
    have := Ideal.mem_map_of_mem τ hw
    rwa [map_natCast] at this
  have hnorm : Ideal.absNorm w.asIdeal = p := by
    have hmem : (p : 𝓞 K) ∈ Ideal.span {((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K)} := by
      rw [← hτ, ← Ideal.inf_eq_mul_of_isCoprime hcop]
      exact ⟨hw, hpτ⟩
    have hdvd := dvd_of_mem h hmem
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (Ideal.absNorm_eq_one_iff.mp h1) hwm.ne_top
    · exact h1
  refine ⟨hnorm, hcop, fun n => ?_⟩
  have hchar : ∀ x : ℕ, (x : 𝓞 K) ∈ w.asIdeal ^ n ↔ p ^ n ∣ x := by
    intro x
    constructor
    · intro hx
      have hx' : (x : 𝓞 K) ∈ (w.asIdeal.map τ) ^ n := by
        rw [← Ideal.map_pow]
        have := Ideal.mem_map_of_mem τ hx
        rwa [map_natCast] at this
      have hmem : (x : 𝓞 K) ∈ Ideal.span {((p ^ n : ℕ) : 𝓞 K)} := by
        rw [Nat.cast_pow, ← Ideal.span_singleton_pow, ← hnorm, ← hτ, mul_pow,
          ← Ideal.inf_eq_mul_of_isCoprime hcop.pow]
        exact ⟨hx, hx'⟩
      exact dvd_of_mem h hmem
    · rintro ⟨c, rfl⟩
      rw [Nat.cast_mul, Nat.cast_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw n)
  haveI : CharP (𝓞 K ⧸ w.asIdeal ^ n) (p ^ n) := ⟨fun x => by
    rw [← map_natCast (Ideal.Quotient.mk (w.asIdeal ^ n)), Ideal.Quotient.eq_zero_iff_mem, hchar]⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcard : Nat.card (𝓞 K ⧸ w.asIdeal ^ n) = p ^ n := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow, hnorm]
  haveI : Finite (𝓞 K ⧸ w.asIdeal ^ n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  have hbij := (ZMod.castHom_injective (𝓞 K ⧸ w.asIdeal ^ n)).bijective_of_nat_card_le
    (by rw [hcard, Nat.card_zmod])
  let e := RingEquiv.ofBijective _ hbij
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk _), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

private theorem dvd_twelve_of_totient_le_two (k : ℕ) (hk : 0 < k) (h : k.totient ≤ 2) : k ∣ 12 := by
  have hk0 : k ≠ 0 := hk.ne'
  have htpos : 0 < k.totient := Nat.totient_pos.mpr hk
  have bound : ∀ d, d ∣ k → d.totient ≤ 2 := fun d hd =>
    le_trans (Nat.le_of_dvd htpos (Nat.totient_dvd_of_dvd hd)) h
  rw [← Nat.factorization_le_iff_dvd hk0 (by norm_num)]
  intro p
  by_cases hp : p.Prime
  · have ht := bound _ (Nat.ordProj_dvd k p)
    rcases Nat.eq_zero_or_pos (k.factorization p) with hm | hm
    · rw [hm]
      exact Nat.zero_le _
    rw [Nat.totient_prime_pow hp hm] at ht
    have hp2 := hp.two_le
    have hpow : 1 ≤ p ^ (k.factorization p - 1) := Nat.one_le_pow _ _ (by omega)
    by_cases h2 : p = 2
    · subst h2
      have h4 : 2 ≤ (12 : ℕ).factorization 2 :=
        (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp (by norm_num)
      by_contra hc
      have h8 : 2 ^ 2 ≤ 2 ^ (k.factorization 2 - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · by_cases h3 : p = 3
      · subst h3
        have h4 : 1 ≤ (12 : ℕ).factorization 3 :=
          (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).mp (by norm_num)
        by_contra hc
        have h9 : 3 ^ 1 ≤ 3 ^ (k.factorization 3 - 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · exfalso
        have hp4 : 4 ≤ p := by
          rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h' | h' | h' | h'
          · exact absurd h' h2
          · exact absurd h' h3
          · subst h'
            norm_num at hp
          · omega
        have : 1 * (p - 1) ≤ p ^ (k.factorization p - 1) * (p - 1) :=
          Nat.mul_le_mul hpow (le_refl (p - 1))
        omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

private theorem units_pm {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (h : Module.finrank ℚ K = 2)
    (t : K ≃ₐ[ℚ] K) (hu : ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 → s = t)
    (hτ : ∀ x : 𝓞 K, x * RingOfIntegers.mapRingEquiv t.toRingEquiv x = ((Algebra.norm ℤ x : ℤ) : 𝓞 K))
    (φ : 𝓞 K →+* ZMod 4) (u : (𝓞 K)ˣ) : u = 1 ∨ u = -1 := by
  have hr : NumberField.Units.rank K = 0 := by
    have h1 := IsTotallyComplex.finrank K
    have h0 := IsTotallyComplex.nrRealPlaces_eq_zero K
    unfold NumberField.Units.rank
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h0]
    omega
  have htors : u ∈ NumberField.Units.torsion K := by
    obtain ⟨⟨ζ, e⟩, hζ, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
    haveI : IsEmpty (Fin (NumberField.Units.rank K)) := by
      rw [hr]
      infer_instance
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hζ
    rw [hζ]
    exact ζ.2
  rw [← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at htors
  have hx : ((u : 𝓞 K) : K) ^ NumberField.Units.torsionOrder K = 1 := by
    have := congrArg (fun v : (𝓞 K)ˣ => ((v : 𝓞 K) : K)) htors
    simpa using this
  have hfin : 0 < orderOf ((u : 𝓞 K) : K) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨_, NumberField.Units.torsionOrder_pos K, hx⟩)
  have htot : (orderOf ((u : 𝓞 K) : K)).totient ≤ 2 := by
    have := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ)
      (IsPrimitiveRoot.orderOf ((u : 𝓞 K) : K)) (IsPrimitiveRoot.orderOf ((u : 𝓞 K) : K))
      (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hfin)
    rwa [Nat.lcm_self, h] at this
  have h12 : ((u : 𝓞 K) : K) ^ 12 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (dvd_twelve_of_totient_le_two _ hfin htot)
  have hu12 : (u : 𝓞 K) ^ 12 = 1 := by
    apply RingOfIntegers.ext
    simpa using h12
  have hfac : ((u : 𝓞 K) - 1) * ((u : 𝓞 K) + 1) * ((u : 𝓞 K) ^ 2 + 1) *
      ((u : 𝓞 K) ^ 2 + (u : 𝓞 K) + 1) * ((u : 𝓞 K) ^ 2 - (u : 𝓞 K) + 1) *
      ((u : 𝓞 K) ^ 4 - (u : 𝓞 K) ^ 2 + 1) = 0 := by
    have e : ((u : 𝓞 K) - 1) * ((u : 𝓞 K) + 1) * ((u : 𝓞 K) ^ 2 + 1) *
        ((u : 𝓞 K) ^ 2 + (u : 𝓞 K) + 1) * ((u : 𝓞 K) ^ 2 - (u : 𝓞 K) + 1) *
        ((u : 𝓞 K) ^ 4 - (u : 𝓞 K) ^ 2 + 1) = (u : 𝓞 K) ^ 12 - 1 := by ring
    rw [e, hu12, sub_self]
  have hφ : ∀ y : ZMod 4, y ^ 2 + 1 ≠ 0 ∧ y ^ 2 + y + 1 ≠ 0 ∧ y ^ 2 - y + 1 ≠ 0 ∧
      y ^ 4 - y ^ 2 + 1 ≠ 0 := by decide
  obtain h' | h6 := mul_eq_zero.mp hfac
  · obtain h' | h5 := mul_eq_zero.mp h'
    · obtain h' | h4 := mul_eq_zero.mp h'
      · obtain h' | h3 := mul_eq_zero.mp h'
        · obtain h1 | h2 := mul_eq_zero.mp h'
          · left
            exact Units.ext (sub_eq_zero.mp h1)
          · right
            apply Units.ext
            rw [Units.val_neg, Units.val_one]
            exact eq_neg_of_add_eq_zero_left h2
        · exfalso
          have := congrArg φ h3
          simp only [map_add, map_pow, map_one, map_zero] at this
          exact (hφ _).1 this
      · exfalso
        have := congrArg φ h4
        simp only [map_add, map_pow, map_one, map_zero] at this
        exact (hφ _).2.1 this
    · exfalso
      have := congrArg φ h5
      simp only [map_add, map_sub, map_pow, map_one, map_zero] at this
      exact (hφ _).2.2.1 this
  · exfalso
    have := congrArg φ h6
    simp only [map_add, map_sub, map_pow, map_one, map_zero] at this
    exact (hφ _).2.2.2 this

open Pointwise in
theorem UpperTheory.V.Ws.Tw.quadFacts :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : IntermediateField ℚ Ω) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∃ τ : 𝓞 K ≃+* 𝓞 K, (∀ c ∉ K.fixingSubgroup, ∀ x : 𝓞 K, c ((x : K) : Ω) = ((τ x : 𝓞 K) : K)) ∧ (∀ I : Ideal (𝓞 K), I * I.map τ = Ideal.span {(Ideal.absNorm I : 𝓞 K)}) ∧ (∀ c ∉ K.fixingSubgroup, ∀ s s' : G K Ω, resQ K s' = c * resQ K s * c⁻¹ → ∀ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), IsPlaceOver A w → IsFrob A (normV w) s → ∃ (w' : HeightOneSpectrum (𝓞 K)) (A' : ValuationSubring Ω), w'.asIdeal = w.asIdeal.map τ ∧ IsPlaceOver A' w' ∧ IsFrob A' (normV w') s') ∧ (∀ (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup → ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w ∧ Ideal.absNorm w.asIdeal = p ∧ IsCoprime w.asIdeal (w.asIdeal.map τ) ∧ ∀ n : ℕ, ∃ φ : 𝓞 K →+* ZMod (p ^ n), RingHom.ker φ = w.asIdeal ^ n) ∧ ((∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup) → ∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1) := by
  intro Ω _ _ _ l _ hl K _ _ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨t, ht, hu, hτ⟩ := exists_conj K h
  let τ : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv t.toRingEquiv
  have hτI : ∀ I : Ideal (𝓞 K), I * I.map τ = Ideal.span {(Ideal.absNorm I : 𝓞 K)} :=
    mul_map τ hτ
  have hres : ∀ c : G ℚ Ω, c ∉ K.fixingSubgroup → ∀ y : K, c (y : Ω) = ((t y : K) : Ω) := by
    intro c hc y
    have hne : c.restrictNormal K ≠ 1 := by
      intro h1
      apply hc
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have := AlgEquiv.restrictNormal_commutes c K ⟨x, hx⟩
      rw [h1] at this
      exact this.symm
    rw [← hu _ hne]
    exact (AlgEquiv.restrictNormal_commutes c K y).symm
  have hval : ∀ (c : G ℚ Ω) (B : ValuationSubring Ω) (z : Ω),
      (c • B).valuation (c z) < 1 ↔ B.valuation z < 1 := fun c B z =>
    UpperTheory.V.val_lt_one (σ := c.toRingEquiv)
      (fun x => ValuationSubring.smul_mem_pointwise_smul_iff (g := c) (S := B) (x := x)) z
  have hle : ∀ (c : G ℚ Ω) (B : ValuationSubring Ω) (z : Ω),
      (c • B).valuation (c z) ≤ 1 ↔ B.valuation z ≤ 1 := by
    intro c B z
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
    exact ValuationSubring.smul_mem_pointwise_smul_iff (g := c) (S := B) (x := z)
  have hsmulK : ∀ (σ : G K Ω) (B : ValuationSubring Ω), σ • B = resQ K σ • B := by
    intro σ B
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
    rfl
  let tw : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K) := fun w =>
    ⟨w.asIdeal.map τ, by haveI := w.isPrime; exact Ideal.map_isPrime_of_equiv τ,
      (Ideal.map_eq_bot_iff_of_injective τ.injective).not.mpr w.ne_bot⟩
  have hmemτ : ∀ (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K),
      x ∈ w.asIdeal.map τ ↔ τ.symm x ∈ w.asIdeal := by
    intro w x
    rw [← Ideal.comap_symm, Ideal.mem_comap]
  have hplace : ∀ c : G ℚ Ω, c ∉ K.fixingSubgroup → ∀ (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → IsPlaceOver (c • A) (tw w) := by
    intro c hc A w hA x
    have e1 : algebraMap K Ω (x : K) = c (algebraMap K Ω ((τ.symm x : 𝓞 K) : K)) := by
      have h2 := hres c hc ((τ.symm x : 𝓞 K) : K)
      have h3 : t ((τ.symm x : 𝓞 K) : K) = (x : K) := by
        show t (t.symm (x : K)) = (x : K)
        exact t.apply_symm_apply _
      rw [h3] at h2
      exact h2.symm
    rw [e1, hval, hA (τ.symm x)]
    exact (hmemτ w x).symm
  have hnormV : ∀ w : HeightOneSpectrum (𝓞 K), normV (tw w) = normV w := by
    intro w
    unfold normV
    exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal (w.asIdeal.map τ) τ rfl).toEquiv).symm
  have hfixσ : ∀ σ : G K Ω, resQ K σ ∈ K.fixingSubgroup := by
    intro σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  have hc0 : ∃ c : G ℚ Ω, c ∉ K.fixingSubgroup := by
    refine ⟨t.liftNormal Ω, fun hmem => ht ?_⟩
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have h1 := AlgEquiv.liftNormal_commutes t Ω y
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
    have h2 := hmem (y : Ω) y.2
    exact h1.symm.trans h2
  have h4 : ∀ (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 →
      Dec (F := ℚ) A ≤ K.fixingSubgroup → ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w ∧
        Ideal.absNorm w.asIdeal = p ∧ IsCoprime w.asIdeal (w.asIdeal.map τ) ∧
        ∀ n : ℕ, ∃ φ : 𝓞 K →+* ZMod (p ^ n), RingHom.ker φ = w.asIdeal ^ n := by
    intro p A hp hA hdec
    have hAtop : A ≠ ⊤ := by
      intro htop
      rw [ValuationSubring.eq_top_iff] at htop
      apply htop
      refine ⟨⟨(p : Ω), ?_, ne_of_lt hA⟩⟩
      rw [Valuation.ne_zero_iff]
      exact_mod_cast hp.ne_zero
    obtain ⟨w, hw⟩ := (places K Ω l A).1 hAtop
    have hpw : (p : 𝓞 K) ∈ w.asIdeal := by
      rw [← hw]
      simpa using hA
    have hne : w.asIdeal ≠ w.asIdeal.map τ := by
      intro heq
      obtain ⟨c, hc⟩ := hc0
      have hcA : IsPlaceOver (c • A) w := by
        have := hplace c hc A w hw
        have hww : tw w = w := HeightOneSpectrum.ext heq.symm
        rwa [hww] at this
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hw hcA
      have hmem : (resQ K σ)⁻¹ * c ∈ Dec (F := ℚ) A := by
        rw [mem_Dec, mul_smul, ← hσ, hsmulK, inv_smul_smul]
      apply hc
      have := K.fixingSubgroup.mul_mem (hfixσ σ) (hdec hmem)
      rwa [mul_inv_cancel_left] at this
    exact ⟨w, hw, split_facts h τ hτI hp w hpw hne⟩
  refine ⟨τ, ?_, hτI, ?_, h4, ?_⟩
  · intro c hc x
    exact hres c hc (x : K)
  · intro c hc s s' hss w A hA hF
    refine ⟨tw w, c • A, rfl, hplace c hc A w hA, ?_⟩
    rw [hnormV]
    have hpt : ∀ z : Ω, s' z = c (s (c⁻¹ z)) := fun z => DFunLike.congr_fun hss z
    refine ⟨?_, ?_⟩
    · show s' • (c • A) = c • A
      rw [hsmulK, hss, mul_smul, mul_smul, inv_smul_smul, ← hsmulK]
      rw [show s • A = A from hF.1]
    · intro x hx
      obtain ⟨y, rfl⟩ : ∃ y, c y = x := ⟨c⁻¹ x, c.apply_symm_apply x⟩
      rw [hle] at hx
      rw [hpt, show c⁻¹ (c y) = y from c.symm_apply_apply y, ← map_pow, ← map_sub, hval]
      exact hF.2 y hx
  · intro hall u
    have h2nu : ¬ IsUnit (2 : 𝓞 K) := by
      intro hunit
      have := hunit.map (Algebra.norm ℤ)
      rw [show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 by simp, Algebra.norm_algebraMap,
        RingOfIntegers.rank, h] at this
      norm_num [Int.isUnit_iff] at this
    obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 K)})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    let w0 : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, by
      intro hb
      rw [hb] at h2M
      have := h2M (Ideal.mem_span_singleton_self 2)
      simp at this⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w0
    have hA2 : A.valuation (2 : Ω) < 1 := by
      have := (hA 2).mpr (h2M (Ideal.mem_span_singleton_self 2))
      have e1 : ((2 : 𝓞 K) : K) = 2 := map_ofNat (algebraMap (𝓞 K) K) 2
      have e2 : algebraMap K Ω ((2 : 𝓞 K) : K) = 2 := by
        rw [e1]
        exact map_ofNat (algebraMap K Ω) 2
      rw [e2] at this
      exact this
    obtain ⟨w, -, -, -, hφ⟩ := h4 2 A Nat.prime_two (by exact_mod_cast hA2) (hall A hA2)
    obtain ⟨φ, -⟩ := hφ 2
    exact units_pm h t hu hτ φ u
