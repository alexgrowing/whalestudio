import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

open UpperTheory.V.KL

private theorem exists_crt_indicator {R : Type} [CommRing R] [IsDedekindDomain R] (a : R) (ha : a ≠ 0)
    (c : Ideal R → Prop) :
    ∃ t : R, ∀ P : Ideal R, P.IsMaximal → a ∈ P → (c P → t - 1 ∈ P) ∧ (¬ c P → t ∈ P) := by
  classical
  have hI : Ideal.span {a} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := (Ideal.finite_factors hI).toFinset)
    (fun v => v.asIdeal) (fun _ => 1)
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun v => if c v.1.asIdeal then 1 else 0)
  refine ⟨y, fun P hP haP => ?_⟩
  have hPb : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at haP
    exact ha haP
  let v : IsDedekindDomain.HeightOneSpectrum R := ⟨P, hP.isPrime, hPb⟩
  have hv : v ∈ (Ideal.finite_factors hI).toFinset := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem]
    exact haP
  have h := hy v hv
  simp only [pow_one] at h
  constructor
  · intro hc
    simpa [v, hc] using h
  · intro hc
    simpa [v, hc] using h

private theorem unimod_iff {R : Type} [CommRing R] {n : ℕ} (v : Fin n → R) :
    Unimodular R v ↔ ∀ P : Ideal R, P.IsMaximal → ¬ ∀ i, v i ∈ P := by
  unfold Unimodular
  constructor
  · intro h P hP hv
    apply hP.ne_top
    rw [eq_top_iff, ← h, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hv i
  · intro h
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    exact h P hP fun i => hle (Ideal.subset_span ⟨i, rfl⟩)

theorem UpperTheory.V.KL.dedekindSR :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R], StableRangeLe R 2 := by
  intro R _ _ n hn r hr
  rw [unimod_iff] at hr
  by_cases hz : ∀ i : Fin n, r i.castSucc = 0
  · refine ⟨fun _ => 1, ?_⟩
    rw [unimod_iff]
    intro P hP hall
    apply hr P hP
    have hl : r (Fin.last n) ∈ P := by
      have := hall ⟨0, by omega⟩
      simp only [one_mul] at this
      rw [hz, zero_add] at this
      exact this
    intro i
    induction i using Fin.lastCases with
    | last => exact hl
    | cast j =>
      rw [hz j]
      exact P.zero_mem
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    obtain ⟨k, hkj⟩ : ∃ k : Fin n, k ≠ j := by
      by_cases h0 : j.val = 0
      · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
        rw [← h] at h0
        simp at h0
      · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
    obtain ⟨t, ht⟩ := exists_crt_indicator (r j.castSucc) hj (fun P => r k.castSucc ∈ P)
    refine ⟨fun i => if i = k then t else 0, ?_⟩
    rw [unimod_iff]
    intro P hP hall
    by_cases haP : r j.castSucc ∈ P
    · have hother : ∀ i : Fin n, i ≠ k → r i.castSucc ∈ P := fun i hi => by
        simpa [hi] using hall i
      have hk : r k.castSucc + t * r (Fin.last n) ∈ P := by
        simpa using hall k
      obtain ⟨h1, h2⟩ := ht P hP haP
      by_cases hc : r k.castSucc ∈ P
      · have htr : t * r (Fin.last n) ∈ P := by
          have := P.sub_mem hk hc
          simpa using this
        rcases hP.isPrime.mem_or_mem htr with htP | hrP
        · apply hP.ne_top
          rw [Ideal.eq_top_iff_one]
          have := P.sub_mem htP (h1 hc)
          simpa using this
        · apply hr P hP
          intro i
          induction i using Fin.lastCases with
          | last => exact hrP
          | cast m =>
            by_cases hm : m = k
            · rw [hm]
              exact hc
            · exact hother m hm
      · apply hc
        have := P.sub_mem hk (P.mul_mem_right (r (Fin.last n)) (h2 hc))
        simpa using this
    · apply haP
      have := hall j
      simpa [Ne.symm hkj] using this
