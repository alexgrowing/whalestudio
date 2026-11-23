import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Af UpperTheory.V.Af.Tw

private theorem int_mem {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω x ∈ A := by
  have hi : IsIntegral ℤ (algebraMap L Ω x) := x.isIntegral_coe.algebraMap
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
  rw [← hy]
  exact y.2

private theorem exists_above {F L Ω : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {v : HeightOneSpectrum (𝓞 F)}
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v ∧ IsPlaceOver A w := by
  let φ : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring (int_mem A)
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap φ :=
    fun x => (A.valuation_lt_one_iff (φ x)).symm
  have hu : ((IsLocalRing.maximalIdeal A).comap φ).under (𝓞 F) = v.asIdeal := by
    ext x
    rw [← hA x, IsScalarTower.algebraMap_apply F L Ω]
    exact (hP (algebraMap (𝓞 F) (𝓞 L) x)).symm
  haveI : ((IsLocalRing.maximalIdeal A).comap φ).LiesOver v.asIdeal := ⟨hu.symm⟩
  exact ⟨⟨(IsLocalRing.maximalIdeal A).comap φ, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _⟩,
    HeightOneSpectrum.ext hu, hP⟩

private theorem normV_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem normV_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) := Nat.card_eq_fintype_card
  rw [e]
  by_contra hlt
  refine FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, Finset.card_univ]
    exact not_le.1 hlt

private theorem two_of_sum {ι : Type} [Fintype ι] (f : ι → ℕ) (hf : ∀ i, 0 < f i) (hs : ∑ i, f i = 2) (a : ι)
    (ha : f a = 1) : ∃ b, b ≠ a ∧ f b = 1 ∧ ∀ c, c = a ∨ c = b := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ha] at hs
  have h1 : ∑ i ∈ Finset.univ.erase a, f i = 1 := by omega
  obtain ⟨b, hb⟩ : (Finset.univ.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at h1
    simp at h1
  rw [← Finset.add_sum_erase _ _ hb] at h1
  have := hf b
  refine ⟨b, Finset.ne_of_mem_erase hb, by omega, fun c => ?_⟩
  by_contra hc
  rw [not_or] at hc
  have h2 : f c ≤ ∑ i ∈ (Finset.univ.erase a).erase b, f i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hc.1, hc.2])
  have := hf c
  omega

theorem UpperTheory.V.Af.Tw.frobSplit :
    UpperTheory.V.Af.Tw.FrobSplit := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hur hA s hs
  classical
  obtain ⟨w, hwv, hw⟩ := exists_above (L := L) hA
  have hq : 1 < normV v := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hle : normV w ≤ normV v := by
    refine normV_le w hq fun x => ?_
    rw [← hw]
    have h3 := hs.2 _ ((A.valuation_le_one_iff _).2 (int_mem A x))
    have h4 : resG F L Ω s (algebraMap L Ω x) = algebraMap L Ω x := s.commutes x
    rw [h4] at h3
    simpa using h3
  haveI := v.isMaximal
  haveI := w.isPrime
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    rw [normV_under' (K := F) w, hwv] at hle
    have h5 : 0 < w.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos _ _
    have h6 : w.asIdeal.inertiaDeg (𝓞 F) ≤ 1 :=
      (Nat.pow_le_pow_iff_right hq).1 (by rwa [pow_one])
    omega
  have hl : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 F) = v → u.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) :=
    fun u hu => ⟨u.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩⟩
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 F)).ne_bot]
    exact hur w hwv
  haveI := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 L) L, h2] at hsum
  obtain ⟨⟨Q, hQ, hQv⟩, hne, h1, hall⟩ := two_of_sum _
    (fun P => Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)) hsum
    ⟨w.asIdeal, hl w hwv⟩ (by simp only [he, hf])
  let w' : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw' : w'.under (𝓞 F) = v := HeightOneSpectrum.ext hQv.over.symm
  have hf' : w'.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_left h1
  refine ⟨w, w', fun h => hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)), fun u => ⟨fun hu => ?_, ?_⟩,
    hw, ?_, ?_⟩
  · rcases hall ⟨u.asIdeal, hl u hu⟩ with h | h
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val h))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro (rfl | rfl)
    exacts [hwv, hw']
  · rw [normV_under' (K := F) w, hwv, hf, pow_one]
  · rw [normV_under' (K := F) w', hw', hf', pow_one]
