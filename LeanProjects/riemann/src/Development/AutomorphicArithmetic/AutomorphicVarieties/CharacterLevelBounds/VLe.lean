import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SelFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LocUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.vLe :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N e n : ℕ) (ψ : G ℚ Ω →* Oˣ), N ≠ 0 → e ≠ 0 → n ≠ 0 → IsOpen (ψ.ker : Set (G ℚ Ω)) → ψ ^ n = 1 →
          V l e ψ ≤ V' l N e ψ + ((N.primeFactors.card * n.factorization l : ℕ) : ℕ∞) * eO l O ∧ (¬ l ∣ n → V l e ψ = V' l N e ψ) := by
  intro Ω _ _ _ l _ O _ _ _ _ _ N e n ψ hN he hn hψ hpow
  classical
  have hPQ := UpperTheory.V.Chr.placesQ Ω
  have key : ∀ c : ℕ∞, (∀ (p : ℕ) (A : ValuationSubring Ω), p.Prime → p ≠ l → A.valuation (p : Ω) < 1 →
      ∀ (U' U : Subgroup (G ℚ Ω)) (h : U' ≤ U), U' = Ine A → U = Dec A →
      Module.length O ↥(resU (rho l e ψ) h).ker ≤ c) →
      V l e ψ ≤ V' l N e ψ + (N.primeFactors.card : ℕ∞) * c := by
    intro c hc
    have hpr : ∀ i : {p // p ∈ N.primeFactors.erase l}, i.1.Prime :=
      fun i => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase i.2)
    choose Af hAf using fun i : {p // p ∈ N.primeFactors.erase l} => hPQ.1 i.1 (hpr i)
    have hsel := UpperTheory.V.Chr.selFam O (G ℚ Ω) (QO l O) (rho l e ψ) ⊤ (shaFam ℚ Ω l) (shaFam ℚ Ω (l * N))
      {p // p ∈ N.primeFactors.erase l} (fun i => Ine (Af i)) (fun i => Dec (Af i))
      (fun i => Ine_le_Dec (Af i)) (fun i => Or.inr ⟨Af i, rfl⟩) (by
        rintro D' (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
        · obtain ⟨p, hp, hAp⟩ := (hPQ.2.1 A (l * N)
            (Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero hN)).1 hA
          by_cases hpl : p = l
          · rw [hpl] at hAp
            exact Or.inl (Or.inl ⟨A, hAp, rfl⟩)
          · right
            have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
            have hpN : p ∈ N.primeFactors.erase l := by
              refine Finset.mem_erase.2 ⟨hpl, Nat.mem_primeFactors.2 ⟨hpP, ?_, hN⟩⟩
              rcases (Nat.Prime.dvd_mul hpP).1 (Nat.dvd_of_mem_primeFactors hp) with h | h
              · exact absurd ((Nat.prime_dvd_prime_iff_eq hpP (Fact.out : l.Prime)).1 h) hpl
              · exact h
            obtain ⟨u, hu, -⟩ := hPQ.2.2 p A (Af ⟨p, hpN⟩) hpP hAp (hAf _)
            exact ⟨⟨p, hpN⟩, u, Subgroup.mem_top u, fun x hx => hu x (Subgroup.mem_inf.1 hx).2⟩
        · exact Or.inl (Or.inr ⟨A, rfl⟩))
    change Module.length O ↥(LocSel (rho l e ψ) ⊤ (shaFam ℚ Ω l)) ≤
      Module.length O ↥(LocSel (rho l e ψ) ⊤ (shaFam ℚ Ω (l * N))) + _
    refine le_trans hsel (add_le_add le_rfl ?_)
    calc _ ≤ ∑ _i : {p // p ∈ N.primeFactors.erase l}, c :=
          Finset.sum_le_sum fun i _ => hc i.1 (Af i) (hpr i) (Finset.ne_of_mem_erase i.2) (hAf i)
            _ _ _ (by simp) (by simp)
      _ = (Fintype.card {p // p ∈ N.primeFactors.erase l} : ℕ∞) * c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N.primeFactors.card : ℕ∞) * c := by
          gcongr
          rw [Fintype.card_coe]
          exact Finset.card_erase_le
  refine ⟨le_trans (key _ fun p A hp hpl hA U' U h h1 h2 => (UpperTheory.V.Chr.locUnr Ω l O e n ψ he hn hψ hpow p A
      hp hpl hA U' U h h1 h2).1) (le_of_eq (by rw [Nat.cast_mul, mul_assoc])), fun hnd => ?_⟩
  refine le_antisymm ?_ (V'_le_V l N e ψ)
  have h0 := key 0 fun p A hp hpl hA U' U h h1 h2 => by
    have h3 := (UpperTheory.V.Chr.locUnr Ω l O e n ψ he hn hψ hpow p A hp hpl hA U' U h h1 h2).1
    rwa [Nat.factorization_eq_zero_of_not_dvd hnd, Nat.cast_zero, zero_mul] at h3
  simpa using h0
