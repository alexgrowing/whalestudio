import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem exists_place_rat {w : ℕ} (hw : w.Prime) :
    ∃ v₀ : HeightOneSpectrum (𝓞 ℚ), ∀ v : HeightOneSpectrum (𝓞 ℚ), ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ v = v₀ := by
  have hne : ((w : ℕ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hw.ne_zero
  have hprime : Prime ((w : ℕ) : 𝓞 ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
    exact Nat.prime_iff_prime_int.mp hw
  have hP : (Ideal.span {((w : ℕ) : 𝓞 ℚ)}).IsPrime := (Ideal.span_singleton_prime hne).mpr hprime
  have hbot : Ideal.span {((w : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hne
  have hmax := hP.isMaximal hbot
  let v₀ : HeightOneSpectrum (𝓞 ℚ) := ⟨Ideal.span {((w : ℕ) : 𝓞 ℚ)}, hP, hbot⟩
  refine ⟨v₀, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [HeightOneSpectrum.ext_iff]
    symm
    exact hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  · rw [hv]
    exact Ideal.subset_span (Set.mem_singleton _)

private theorem finite_above {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(n : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hn
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Fr.st_set :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l w N : ℕ), l.Prime → w.Prime → N ≠ 0 → ∀ (C : Type) [Group C] (κ : G ℚ Ω →* C), (∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → Ine (F := ℚ) A ≤ κ.ker) → ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v₀ : HeightOneSpectrum (𝓞 ℚ)), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ v = v₀) ∧ ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), IsPlaceOver A v → (v ∈ S ↔ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ v = v₀ ∨ ¬ Ine (F := ℚ) A ≤ κ.ker) := by
  intro Ω _ _ _ l w N hl hw hN C _ κ hκ
  classical
  obtain ⟨v₀, hv₀⟩ := exists_place_rat hw
  have hT := finite_above (n := l * w * N) (mul_ne_zero (mul_ne_zero hl.ne_zero hw.ne_zero) hN)
  have key : ∀ (A A' : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
      IsPlaceOver A' v → Ine (F := ℚ) A ≤ κ.ker → Ine (F := ℚ) A' ≤ κ.ker := by
    intro A A' v hA hA' hle τ hτ
    obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isPlaceOver hA hA'
    have h1 := hle (GlobalTheory.Cut.ShaBound.conj_mem_Ine' hτ)
    have h2 := κ.normal_ker.conj_mem _ h1 σ
    simpa [mul_assoc] using h2
  have hN' : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
      ¬ Ine (F := ℚ) A ≤ κ.ker → ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro A v hA hne
    have h1 : A.valuation (N : Ω) < 1 := by
      by_contra h
      exact hne (hκ A h)
    rw [← hA (N : 𝓞 ℚ)]
    simpa using h1
  refine ⟨hT.toFinset.filter (fun v => ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ v = v₀ ∨
    ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ ¬ Ine (F := ℚ) A ≤ κ.ker), v₀, hv₀, ?_⟩
  intro v A hA
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h | h | ⟨A', hA', hne⟩⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (fun hle => hne (key A A' v hA hA' hle)))
  · intro h
    refine ⟨?_, ?_⟩
    · have hmem : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨ ((w : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ∨
          ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ((hv₀ v).mpr h))
        · exact Or.inr (Or.inr (hN' A v hA h))
      push_cast
      rcases hmem with h | h | h
      · exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h)
      · exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h)
      · exact v.asIdeal.mul_mem_left _ h
    · rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨A, hA, h⟩)
