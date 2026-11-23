import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree

open IsLocalRing

private theorem UpperTheory.V.Pr.npe_height_le_one {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (m : Ideal B) [m.IsPrime] {f : B} (hf : f ≠ 0)
    (h : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → p ≤ m → f ∈ p) : m.height ≤ 1 := by
  by_cases hm : m = ⊥
  · subst hm
    simp
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.mem_iUnion, id, SetLike.mem_coe]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    have hPp : P.IsPrime := hP.1.1
    have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
    have hP1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
    have hfP : f ∈ P := h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P)
        ((Ideal.span_singleton_le_iff_mem _).mpr hfP)
    have hQp : Q.IsPrime := hQ.1.1
    have hfQ : f ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
    have hQ0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)
    refine ⟨Q, hQ, ?_⟩
    rcases hQP.eq_or_lt with e | hlt
    · exact e ▸ hxP
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hQ0
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hP1)
      simp at h3
      exact absurd h3 (by decide)
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
    (fun i hi _ _ => hi.1.1)).mp hsub
  have hPp : P.IsPrime := hP.1.1
  exact (Ideal.height_mono hmP).trans
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)

private theorem UpperTheory.V.Pr.npe_dim_one {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (Q : Ideal R) [Q.IsPrime] {f : R} (hfm : f ∈ maximalIdeal R) (hf : f ∉ Q) :
    ∃ p : Ideal R, p.IsPrime ∧ Q ≤ p ∧ f ∉ p ∧ ringKrullDim (R ⧸ p) = 1 := by
  obtain ⟨p, ⟨hp, hQp, hfp⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {p : Ideal R | p.IsPrime ∧ Q ≤ p ∧ f ∉ p}
    ⟨Q, inferInstance, le_rfl, hf⟩
  refine ⟨p, hp, hQp, hfp, ?_⟩
  haveI : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hf0 : Ideal.Quotient.mk p f ≠ 0 := fun h => hfp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hh : (maximalIdeal (R ⧸ p)).height ≤ 1 := by
    refine UpperTheory.V.Pr.npe_height_le_one _ hf0 fun P hP hP0 _ => ?_
    by_contra hfP
    have hle : p ≤ P.comap (Ideal.Quotient.mk p) := fun x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact P.zero_mem
    refine hmax (P.comap (Ideal.Quotient.mk p))
      ⟨Ideal.comap_isPrime _ _, hQp.trans hle, hfP⟩ (lt_of_le_of_ne hle fun e => hP0 ?_)
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : x ∈ p := by rw [e]; exact hy
    exact Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr this)
  have hfm' : Ideal.Quotient.mk p f ∈ maximalIdeal (R ⧸ p) := by
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    exact map_nonunit _ f hfm
  have hlt : (⊥ : Ideal (R ⧸ p)) < maximalIdeal (R ⧸ p) :=
    bot_lt_iff_ne_bot.mpr fun e => hf0 (by simpa [e] using hfm')
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (maximalIdeal (R ⧸ p)).height = 1 := le_antisymm hh (le_trans le_add_self h1)
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h2]
  rfl

private theorem UpperTheory.V.Pr.npe_chain {R : Type} [CommRing R] (q : LTSeries (PrimeSpectrum R))
    (J : Ideal R) (N : ℕ) (hN : N + 1 ≤ q.length) (hJ : J ≤ (q ⟨1, by omega⟩).asIdeal) :
    (N : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) := by
  rw [ringKrullDim_quotient, Order.le_krullDim_iff]
  exact ⟨{ length := N
           toFun := fun i => ⟨q ⟨i + 1, by omega⟩,
             hJ.trans (q.monotone (a := ⟨1, by omega⟩) (b := ⟨i + 1, by omega⟩) (by simp [Fin.le_def]))⟩
           step := fun i => q.strictMono (by simp [Fin.lt_def]) }, rfl⟩

theorem UpperTheory.V.Pr.nicePrimeEx :
    UpperTheory.V.Pr.NicePrimeEx := by
  classical
  intro R _ _ _ ϖ hϖ N hN ι _ a ha I hI
  rw [UpperTheory.V.Pr.qdim, ringKrullDim_quotient, Order.le_krullDim_iff] at hI
  obtain ⟨l, hl⟩ := hI
  obtain ⟨s, hs, hI0, hlast⟩ : ∃ s : LTSeries (PrimeSpectrum R), N + 1 ≤ s.length ∧
      I ≤ s.head.asIdeal ∧ ϖ ∈ s.last.asIdeal := by
    let t : LTSeries (PrimeSpectrum R) := l.map Subtype.val (fun _ _ h => h)
    have ht : t.length = N + 1 := hl
    have hh : I ≤ t.head.asIdeal := l.head.2
    have hle : t.last ≤ closedPoint R := le_maximalIdeal t.last.2.ne_top
    rcases hle.eq_or_lt with e | hlt
    · exact ⟨t, ht.ge, hh, by rw [e]; exact hϖ⟩
    · exact ⟨t.snoc _ hlt, by simp [ht], by simpa using hh, by rw [RelSeries.last_snoc]; exact hϖ⟩
  obtain ⟨q, hq1, hqlen, hqh, -⟩ := PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last s hlast
  have hq : N + 1 ≤ q.length := hqlen ▸ hs
  have e1 : (1 : Fin (q.length + 1)) = ⟨1, by omega⟩ := by
    ext; simp [Nat.mod_eq_of_lt (show 1 < q.length + 1 by omega)]
  rw [e1] at hq1
  set Q := q ⟨1, by omega⟩ with hQ
  have hIQ : I ≤ Q.asIdeal := by
    rw [hqh] at hI0
    exact hI0.trans (q.monotone (a := 0) (Fin.zero_le _))
  have hQ2 : Q < q ⟨2, by omega⟩ := q.strictMono (by simp [Fin.lt_def])
  obtain ⟨g, hg, hgQ⟩ := SetLike.exists_of_lt (show Q.asIdeal < (q ⟨2, by omega⟩).asIdeal from hQ2)
  have hgm : g ∈ maximalIdeal R := le_maximalIdeal (q ⟨2, by omega⟩).2.ne_top hg
  have hna : ∀ i, ∃ x ∈ a i, x ∉ Q.asIdeal := fun i =>
    SetLike.not_le_iff_exists.mp fun h => (UpperTheory.V.Pr.npe_chain q (a i) N hq h).not_gt (ha i)
  choose x hxa hxQ using hna
  haveI := Fintype.ofFinite ι
  have hf : g * ∏ i, x i ∉ Q.asIdeal := fun h => by
    rcases Q.2.mem_or_mem h with h | h
    · exact hgQ h
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hxQ i hi
  obtain ⟨p, hp, hQp, hfp, hd⟩ := UpperTheory.V.Pr.npe_dim_one Q.asIdeal (Ideal.mul_mem_right _ _ hgm) hf
  refine ⟨p, hp, hIQ.trans hQp, hd, hQp hq1, fun i hi => hfp (Ideal.mul_mem_left _ _ ?_)⟩
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem x (Finset.mem_univ i)) (hi (hxa i))
