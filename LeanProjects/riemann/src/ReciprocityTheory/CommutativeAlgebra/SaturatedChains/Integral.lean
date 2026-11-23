import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain

namespace ReciprocityTheory.CA

private theorem exists_prime_over_lemma {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (p : Ideal A) [p.IsPrime] (I : Ideal B)
    (hI : I.comap (algebraMap A B) ≤ p) :
    ∃ Q : Ideal B, I ≤ Q ∧ Q.IsPrime ∧ Q.comap (algebraMap A B) = p := by
  first
  | exact Ideal.exists_ideal_over_prime_of_isIntegral p I hI
  | exact Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p I hI
  | (obtain ⟨Q, h1, h2, h3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p I hI
     exact ⟨Q, h1, h2, h3⟩)

theorem exists_ltSeries_lift_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (h : Function.Injective (algebraMap A B))
    (l : LTSeries (PrimeSpectrum A)) :
    ∃ l' : LTSeries (PrimeSpectrum B), l'.length = l.length ∧
      l'.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal := by
  suffices H : ∀ n, ∀ l : LTSeries (PrimeSpectrum A), l.length = n →
      ∃ l' : LTSeries (PrimeSpectrum B), l'.length = l.length ∧
        l'.last.asIdeal.comap (algebraMap A B) = l.last.asIdeal by
    exact H _ l rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    obtain ⟨Q, -, hQ, hQc⟩ := exists_prime_over_lemma l.last.asIdeal ⊥ (by
      first
      | (rw [Ideal.comap_bot_of_injective _ h]; exact bot_le)
      | (intro y hy
         rw [Ideal.mem_comap, Ideal.mem_bot] at hy
         rw [show y = 0 from h (by rw [hy, map_zero])]
         exact Ideal.zero_mem _))
    refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, ?_, ?_⟩
    · simp [hl]
    · simpa using hQc
  | succ n ih =>
    intro l hl
    have hne : l.length ≠ 0 := by omega
    obtain ⟨l', hlen, hlast⟩ := ih l.eraseLast (by simp [hl])
    have hlt : l.eraseLast.last < l.last := l.eraseLast_last_rel_last hne
    obtain ⟨Q, hQle, hQ, hQc⟩ := exists_prime_over_lemma l.last.asIdeal l'.last.asIdeal (by
      rw [hlast]
      exact le_of_lt hlt)
    have hlt' : l'.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hQle ?_
      intro heq
      have hc := congrArg (fun q : PrimeSpectrum B => q.asIdeal.comap (algebraMap A B)) heq
      simp only at hc
      rw [hlast, hQc] at hc
      exact (ne_of_lt hlt) (PrimeSpectrum.ext hc)
    refine ⟨l'.snoc ⟨Q, hQ⟩ hlt', ?_, ?_⟩
    · first
      | (simp [hlen, hl]; done)
      | (simp [hlen, hl]; omega)
    · simpa using hQc

theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  have hmono : StrictMono (fun q : PrimeSpectrum B =>
      (⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩ : PrimeSpectrum A)) := by
    intro q q' hqq'
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hqq' ⊢
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hqq'
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff (le_of_lt hqq') ⟨hx, hx'⟩
      (Algebra.IsIntegral.isIntegral x)
  apply le_antisymm
  · first
    | exact Order.krullDim_le_of_strictMono _ hmono
    | (apply iSup_le
       intro l'
       exact le_iSup_of_le (l'.map _ hmono) le_rfl)
  · apply iSup_le
    intro l
    obtain ⟨l', hlen, -⟩ := exists_ltSeries_lift_of_isIntegral hinj l
    rw [← hlen]
    exact le_iSup (fun p : LTSeries (PrimeSpectrum B) => (p.length : WithBot ℕ∞)) l'

theorem ringKrullDim_quotient_eq_quotient_comap_of_isIntegral {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (I : Ideal B) :
    ringKrullDim (B ⧸ I) = ringKrullDim (A ⧸ I.comap (algebraMap A B)) := by
  haveI : Algebra.IsIntegral (A ⧸ I.comap (algebraMap A B)) (B ⧸ I) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.quotient I
  exact ringKrullDim_eq_of_isIntegral_of_injective Ideal.algebraMap_quotient_injective

end ReciprocityTheory.CA
