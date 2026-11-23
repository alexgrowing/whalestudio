import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree

open PrimeSpectrum in
private theorem UpperTheory.V.Pr.exp_product_chart_local {X : Type} [TopologicalSpace X] {C : Type} [CommRing C]
    {j : PrimeSpectrum C → X} (hj : Topology.IsOpenEmbedding j) {Z : Set X} (hZ : IsIrreducible Z)
    {c : PrimeSpectrum C} (hc : j c ∈ Z) :
    ∃ q : PrimeSpectrum C, q ⤳ c ∧ Z ⊆ closure {j q} := by
  have h1 : IsIrreducible (j ⁻¹' Z) := ⟨⟨c, hc⟩, hZ.isPreirreducible.preimage hj⟩
  obtain ⟨q, hq⟩ := QuasiSober.sober h1.closure isClosed_closure
  refine ⟨q, hq.specializes (subset_closure hc), ?_⟩
  have h2 : Z ⊆ closure (Z ∩ Set.range j) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hZ.isPreirreducible hj.isOpen_range
      ⟨j c, hc, c, rfl⟩
  refine h2.trans (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨hy, y, rfl⟩
  have h3 : q ⤳ y := hq.specializes (subset_closure hy)
  exact specializes_iff_mem_closure.mp (h3.map hj.continuous)

open PrimeSpectrum in
theorem UpperTheory.V.Pr.chartOfFlat :
    UpperTheory.V.Pr.ChartOfFlat := by
  intro X _ C _ j hj R _ _ _ _
  have hg : GeneralizingMap (PrimeSpectrum.comap (algebraMap C R)) :=
    Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance
  have hc : Continuous (j ∘ PrimeSpectrum.comap (algebraMap C R)) :=
    hj.continuous.comp (PrimeSpectrum.continuous_comap _)
  refine ⟨hc, rfl, ?_, ?_⟩
  · intro P hP
    refine ⟨isIrreducible_singleton.closure, ?_⟩
    intro Z hZ hle
    have hmem : j (PrimeSpectrum.comap (algebraMap C R) P) ∈ Z := hle (subset_closure rfl)
    obtain ⟨q, hq, hZq⟩ := UpperTheory.V.Pr.exp_product_chart_local hj hZ hmem
    obtain ⟨P', hP', rfl⟩ := hg hq
    have h1 : P' ≤ P := (PrimeSpectrum.le_iff_specializes _ _).mpr hP'
    have h2 : P.asIdeal ≤ P'.asIdeal := hP.2 ⟨P'.isPrime, bot_le⟩ h1
    have h3 : P' = P := le_antisymm h1 h2
    subst h3
    exact hZq
  · intro Y hY hx
    obtain ⟨q, hq, hYq⟩ := UpperTheory.V.Pr.exp_product_chart_local hj hY.1 hx
    obtain ⟨P', -, rfl⟩ := hg hq
    obtain ⟨p, hp, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := P'.asIdeal) bot_le
    refine ⟨⟨p, hp.1.1⟩, hp, ?_⟩
    have h1 : (⟨p, hp.1.1⟩ : PrimeSpectrum R) ⤳ P' := (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 : Y ⊆ closure {(j ∘ PrimeSpectrum.comap (algebraMap C R)) ⟨p, hp.1.1⟩} :=
      hYq.trans (closure_minimal
        (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp (h1.map hc))) isClosed_closure)
    exact Set.Subset.antisymm (hY.2 isIrreducible_singleton.closure h2) h2
