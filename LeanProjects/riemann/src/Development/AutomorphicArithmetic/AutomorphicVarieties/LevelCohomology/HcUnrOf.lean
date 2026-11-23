import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.unrOf :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k : Type) [Field k] (γ : G ℚ Ω →* kˣ) (K : Subgroup (G ℚ Ω)) [K.Normal], K ≤ γ.ker → ∀ (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T : Finset ℕ) (z : GS Ω SP → k), (∀ g h, z (toGS Ω SP (g * h)) = z (toGS Ω SP g) + (γ g : k) * z (toGS Ω SP h)) → (∀ v ∈ SP, (∃ p ∈ T, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) ∨ ∃ A, IsPlaceOver A v ∧ ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z (toGS Ω SP g) = 0) → ∀ A : ValuationSubring Ω, (∀ p ∈ T, ¬ A.valuation (p : Ω) < 1) → ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z (toGS Ω SP g) = 0 := by
  intro Ω _ _ _ k _ γ K hKn hK SP T z hz hS A hA g hg hgK
  have h1 : z (toGS Ω SP 1) = 0 := by
    have e := hz 1 1
    rw [mul_one, map_one γ, Units.val_one, one_mul] at e
    linear_combination (-1 : k) * e
  obtain ⟨hTop, hPl, -, hAb⟩ := UpperTheory.V.Kum.placeDict ℚ Ω
  by_cases hAT : A = ⊤
  · subst hAT
    rw [hTop, Subgroup.mem_bot] at hg
    subst hg
    exact h1
  obtain ⟨v, hv⟩ := hPl A hAT
  by_cases hvS : v ∈ SP
  · rcases hS v hvS with ⟨p, hpT, hp⟩ | ⟨A', hA', hz0⟩
    · exact absurd ((hAb A v p hv).mpr hp) (hA p hpT)
    · obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA' hv
      subst hσ
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) A' := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg
      have hcK : σ⁻¹ * g * σ ∈ K := by
        have e := hKn.conj_mem g hgK σ⁻¹
        simpa only [inv_inv] using e
      have e0 := hz0 _ hc hcK
      have e1 := hz g σ
      have e2 := hz σ (σ⁻¹ * g * σ)
      have hγ : γ g = 1 := hK hgK
      have hm : σ * (σ⁻¹ * g * σ) = g * σ := by group
      rw [hγ, Units.val_one, one_mul] at e1
      rw [hm, e0, mul_zero, add_zero] at e2
      linear_combination e2 - e1
  · have hN : g ∈ NS Ω SP := by
      unfold NS
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hg⟩
    have e : toGS Ω SP g = toGS Ω SP 1 := by
      rw [map_one]
      exact (QuotientGroup.eq_one_iff g).mpr hN
    rw [e]
    exact h1
