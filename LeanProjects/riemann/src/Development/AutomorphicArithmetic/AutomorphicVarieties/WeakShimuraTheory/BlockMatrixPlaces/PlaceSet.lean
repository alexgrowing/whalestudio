import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.placeSet :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (B : ValuationSubring Ω), (∀ p ∈ S, p.Prime) → l ∈ S → B.valuation (l : Ω) < 1 →
          ∃ (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (Av : S' → ValuationSubring Ω) (v0 : S'), ContainsAbove S' l ∧ (∀ v, IsPlaceOver (Av v) v.1) ∧ Av v0 = B ∧ ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal ∧
            ∀ K : Subgroup (G ℚ Ω), K.Normal → IsClosed (K : Set (G ℚ Ω)) → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ K := by
  intro Ω _ _ _ l hl S B hS hlS hB
  classical
  have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 ℚ) | ∃ p ∈ S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} := by
    have e : {v : HeightOneSpectrum (𝓞 ℚ) | ∃ p ∈ S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =
        ⋃ p ∈ (S : Set ℕ), {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 ℚ)}} := by
      ext v
      simp [Ideal.dvd_span_singleton]
    rw [e]
    refine S.finite_toSet.biUnion fun p hp => Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (hS p hp).ne_zero
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places ℚ Ω l B
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := (h3 w hw).1 hB
  have hex : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ (v = w → A = B) := by
    intro v
    by_cases e : v = w
    · exact ⟨B, e ▸ hw, fun _ => rfl⟩
    · obtain ⟨A, hA⟩ := (exists_isPlaceOver Ω v : ∃ A : ValuationSubring Ω, IsPlaceOver A v)
      exact ⟨A, hA, fun h => absurd h e⟩
  choose f hf hf' using hex
  refine ⟨hfin.toFinset, fun v => f v.1, ⟨w, hfin.mem_toFinset.2 ⟨l, hlS, hlw⟩⟩,
    fun v hv => hfin.mem_toFinset.2 ⟨l, hlS, hv⟩, fun v => hf v.1, hf' w rfl, hlw, fun K hK hc hI => ?_⟩
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨v, hv, A, hA, hg⟩ := hg
  refine hI A (fun p hp h => hv ?_) hg
  refine Finset.mem_coe.2 (hfin.mem_toFinset.2 ⟨p, hp, (hA ((p : ℕ) : 𝓞 ℚ)).1 ?_⟩)
  simpa using h
