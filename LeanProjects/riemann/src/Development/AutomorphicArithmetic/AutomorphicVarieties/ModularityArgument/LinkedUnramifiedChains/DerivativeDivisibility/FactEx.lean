import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime

open Polynomial UniqueFactorizationMonoid in
theorem UpperTheory.V.J.factEx :
    UpperTheory.V.J.FactEx := by
  intro Λ _ _ _ χ hχ
  classical
  have hinjK : Function.Injective (algebraMap Λ (FractionRing Λ)) :=
    IsFractionRing.injective Λ (FractionRing Λ)
  have hinj : Function.Injective (Polynomial.map (algebraMap Λ (FractionRing Λ))) :=
    Polynomial.map_injective _ hinjK
  set P := χ.map (algebraMap Λ (FractionRing Λ)) with hPdef
  have hP : P ≠ 0 := (hχ.map _).ne_zero
  have hmon : ∀ f ∈ normalizedFactors P, f.Monic := by
    intro f hf
    rw [← normalize_normalized_factor f hf]
    exact Polynomial.monic_normalize (prime_of_normalized_factor f hf).ne_zero
  have hlift : ∀ f ∈ normalizedFactors P,
      ∃ g : Λ[X], g.Monic ∧ g.map (algebraMap Λ (FractionRing Λ)) = f := by
    intro f hf
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing Λ) hχ
      (dvd_of_mem_normalizedFactors hf)
    rw [(hmon f hf).leadingCoeff, C_1, mul_one] at hg
    refine ⟨g, Polynomial.monic_of_injective hinjK ?_, hg⟩
    rw [hg]
    exact hmon f hf
  choose! L hLm hLmap using hlift
  have hprod : χ = ((normalizedFactors P).map L).prod := by
    apply hinj
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    have h1 : (normalizedFactors P).map
        ((Polynomial.map (algebraMap Λ (FractionRing Λ))) ∘ L) = normalizedFactors P := by
      conv_rhs => rw [← Multiset.map_id (normalizedFactors P)]
      exact Multiset.map_congr rfl (fun f hf => hLmap f hf)
    rw [h1]
    refine eq_of_monic_of_associated (hχ.map _) ?_ (prod_normalizedFactors hP).symm
    exact Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb) monic_one hmon
  have memG : ∀ x ∈ (normalizedFactors P).map L,
      x.Monic ∧ Irreducible (x.map (algebraMap Λ (FractionRing Λ))) := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨hLm f hf, by rw [hLmap f hf]; exact irreducible_of_normalized_factor f hf⟩
  let e := ((normalizedFactors P).map L).toFinset.equivFin
  refine ⟨_, fun i => (e.symm i).1, fun i => ((normalizedFactors P).map L).count (e.symm i).1,
    ⟨fun i => (memG _ (Multiset.mem_toFinset.1 (e.symm i).2)).1,
     fun i => (memG _ (Multiset.mem_toFinset.1 (e.symm i).2)).2,
     fun i j h => e.symm.injective (Subtype.ext h),
     fun i => Multiset.count_pos.2 (Multiset.mem_toFinset.1 (e.symm i).2), ?_⟩⟩
  refine hprod.trans ?_
  rw [Finset.prod_multiset_count, ← Finset.prod_coe_sort]
  exact Fintype.prod_equiv e _ _ (fun x => by simp)
