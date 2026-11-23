import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing UpperTheory.V.Alg

private theorem a3one_of_factSplit_of_countCont (R : Type) [CommRing R] [IsNoetherianRing R] (I p : Ideal R) [hp : p.IsPrime]
    (a : R) (h : ∀ N : ℕ, ∃ s, s ∉ p ∧ s * a ∈ p ^ N ⊔ I) : ∃ y, y ∉ p ∧ y * a ∈ I := by
  by_cases hIp : I ≤ p
  swap
  · obtain ⟨y, hyI, hyp⟩ := Set.not_subset.mp hIp
    exact ⟨y, hyp, I.mul_mem_right a hyI⟩
  haveI hq : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  haveI : IsNoetherianRing (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) :=
    IsLocalization.isNoetherianRing (p.map (Ideal.Quotient.mk I)).primeCompl _ inferInstance
  have hKrull := Ideal.iInf_pow_eq_bot_of_isLocalRing
    (IsLocalRing.maximalIdeal (Localization.AtPrime (p.map (Ideal.Quotient.mk I))))
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hmem : algebraMap (R ⧸ I) (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
      (Ideal.Quotient.mk I a) ∈ ⨅ i : ℕ,
        IsLocalRing.maximalIdeal (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) ^ i := by
    rw [Submodule.mem_iInf]
    intro N
    obtain ⟨s, hs, hsa⟩ := h N
    have h1 : Ideal.Quotient.mk I (s * a) ∈ (p.map (Ideal.Quotient.mk I)) ^ N := by
      rw [← Ideal.map_pow, Ideal.mem_quotient_iff_mem_sup]
      exact hsa
    have h2 : algebraMap (R ⧸ I) (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
        (Ideal.Quotient.mk I (s * a)) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) ^ N := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ h1
    have hs' : Ideal.Quotient.mk I s ∉ p.map (Ideal.Quotient.mk I) := by
      rwa [Ideal.mem_quotient_iff_mem hIp]
    have hsu : IsUnit (algebraMap (R ⧸ I) (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
        (Ideal.Quotient.mk I s)) :=
      IsLocalization.map_units (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))
        (⟨Ideal.Quotient.mk I s, hs'⟩ : (p.map (Ideal.Quotient.mk I)).primeCompl)
    rw [map_mul, map_mul] at h2
    obtain ⟨u, hu⟩ := hsu
    have := Ideal.mul_mem_left _ (↑u⁻¹ : Localization.AtPrime (p.map (Ideal.Quotient.mk I))) h2
    rwa [← hu, ← mul_assoc, Units.inv_mul, one_mul] at this
  rw [hKrull, Submodule.mem_bot] at hmem
  obtain ⟨⟨c, hc⟩, hca⟩ := (IsLocalization.map_eq_zero_iff (p.map (Ideal.Quotient.mk I)).primeCompl
    (Localization.AtPrime (p.map (Ideal.Quotient.mk I))) _).mp hmem
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hc' : Ideal.Quotient.mk I y ∉ p.map (Ideal.Quotient.mk I) := hc
  refine ⟨y, fun hy => hc' (Ideal.mem_map_of_mem _ hy), ?_⟩
  have hca' : Ideal.Quotient.mk I y * Ideal.Quotient.mk I a = 0 := hca
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hca'
  exact hca'

theorem UpperTheory.exists_not_mem_mul_mem_ideal_of_forall_prime_pow_sup :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I p P : Ideal R), p.IsPrime → I ≤ p → (∀ a ∈ P, ∀ N : ℕ, ∃ s, s ∉ p ∧ s * a ∈ p ^ N ⊔ I) → ∃ y, y ∉ p ∧ ∀ a ∈ P, y * a ∈ I := by
  classical
  intro R _ _ I p P hp hIp hP
  haveI := hp
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian P : P.FG)
  have h1p : (1 : R) ∉ p := fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  have hgen : ∀ T : Finset R, (T : Set R) ⊆ P → ∃ y, y ∉ p ∧ ∀ a ∈ T, y * a ∈ I := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨1, h1p, by simp⟩
    | insert b T hb ih =>
      intro hT
      obtain ⟨y1, hy1, hy1'⟩ := ih (fun z hz => hT (Finset.mem_insert_of_mem hz))
      obtain ⟨y2, hy2, hy2'⟩ := a3one_of_factSplit_of_countCont R I p b (hP b (hT (Finset.mem_insert_self b T)))
      refine ⟨y1 * y2, fun h => (hp.mem_or_mem h).elim hy1 hy2, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rw [mul_assoc]
        exact I.mul_mem_left _ hy2'
      · rw [mul_comm y1, mul_assoc]
        exact I.mul_mem_left _ (hy1' z hz)
  obtain ⟨y, hy, hyS⟩ := hgen S (by rw [← hS]; exact Submodule.subset_span)
  refine ⟨y, hy, fun a ha => ?_⟩
  rw [← hS] at ha
  induction ha using Submodule.span_induction with
  | mem z hz => exact hyS z hz
  | zero => simp
  | add u v _ _ hu hv =>
    rw [mul_add]
    exact I.add_mem hu hv
  | smul r u _ hu =>
    rw [smul_eq_mul, mul_left_comm]
    exact I.mul_mem_left r hu
