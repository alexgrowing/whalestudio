import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cl_mvps_fin {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : Module.Finite A (S ⧸ I)) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  classical
  have toP : ∀ K : Ideal S, Module.Finite A (S ⧸ K) →
      ∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ K := by
    intro K hK
    obtain ⟨T, hT⟩ := hK.fg_top
    choose l hl using fun q : S ⧸ K => Ideal.Quotient.mk_surjective q
    refine ⟨T.image l, fun s => ?_⟩
    have himg : (Ideal.Quotient.mkₐ A K).toLinearMap '' ((T.image l : Finset S) : Set S) = (T : Set (S ⧸ K)) := by
      ext q
      simp [hl]
    have hs : Ideal.Quotient.mk K s ∈ Submodule.map (Ideal.Quotient.mkₐ A K).toLinearMap
        (Submodule.span A ((T.image l : Finset S) : Set S)) := by
      rw [Submodule.map_span, himg, hT]
      exact Submodule.mem_top
    obtain ⟨t, ht, hts⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [← Ideal.Quotient.eq]
    simpa using hts.symm
  have ofP : ∀ K : Ideal S, (∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ K) →
      Module.Finite A (S ⧸ K) := by
    rintro K ⟨F, hF⟩
    refine ⟨⟨F.image (Ideal.Quotient.mk K), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨t, ht, hst⟩ := hF s
    have h1 : Ideal.Quotient.mk K s = (Ideal.Quotient.mkₐ A K).toLinearMap t := by
      simpa [Ideal.Quotient.eq] using hst
    have h2 := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ A K).toLinearMap) ht
    have himg : (Ideal.Quotient.mkₐ A K).toLinearMap '' (F : Set S) = ((F.image (Ideal.Quotient.mk K) : Finset (S ⧸ K)) : Set (S ⧸ K)) := by
      ext q
      simp
    rw [Submodule.map_span, himg] at h2
    rw [h1]
    exact h2
  obtain ⟨F1, hF1⟩ := toP I h
  have hpow : ∀ n : ℕ, ∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ I ^ n := by
    intro n
    induction n with
    | zero => exact ⟨∅, fun s => ⟨0, Submodule.zero_mem _, by simp⟩⟩
    | succ n ih =>
      obtain ⟨Fn, hFn⟩ := ih
      obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (I ^ n) : (I ^ n).FG)
      refine ⟨Fn ∪ (F1 ×ˢ G).image (fun p => p.1 * p.2), fun s => ?_⟩
      obtain ⟨t, ht, hst⟩ := hFn s
      rw [← hG, Submodule.mem_span_finset] at hst
      obtain ⟨c, -, hc⟩ := hst
      choose u hu hcu using fun g => hF1 (c g)
      refine ⟨t + ∑ g ∈ G, u g * g, ?_, ?_⟩
      · refine Submodule.add_mem _ (Submodule.span_mono ?_ ht) (Submodule.sum_mem _ fun g hg => ?_)
        · exact Finset.coe_subset.mpr Finset.subset_union_left
        · have h3 := Submodule.mem_map_of_mem (f := LinearMap.mulRight A g) (hu g)
          rw [Submodule.map_span] at h3
          refine Submodule.span_mono ?_ h3
          rintro _ ⟨f, hf, rfl⟩
          rw [Finset.coe_union, Finset.coe_image]
          right
          exact ⟨(f, g), Finset.mem_product.mpr ⟨hf, hg⟩, by simp⟩
      · have hct : s - t = ∑ g ∈ G, c g * g := by
          rw [← hc]
          simp [smul_eq_mul]
        have he : s - (t + ∑ g ∈ G, u g * g) = ∑ g ∈ G, (c g - u g) * g := by
          calc s - (t + ∑ g ∈ G, u g * g) = (s - t) - ∑ g ∈ G, u g * g := by ring
            _ = ∑ g ∈ G, c g * g - ∑ g ∈ G, u g * g := by rw [hct]
            _ = ∑ g ∈ G, (c g - u g) * g := by
              rw [← Finset.sum_sub_distrib]
              simp [sub_mul]
        rw [he, pow_succ']
        refine Ideal.sum_mem _ fun g hg => Ideal.mul_mem_mul (hcu g) ?_
        rw [← hG]
        exact Submodule.subset_span hg
  obtain ⟨F, hF⟩ := hpow N
  exact ofP J ⟨F, fun s => (hF s).imp fun t ⟨ht, hst⟩ => ⟨ht, hN hst⟩⟩

private theorem cl_mvps_max {O σ : Type} [CommRing O] [IsLocalRing O] (g : MvPowerSeries σ O) :
    g ∈ maximalIdeal (MvPowerSeries σ O) ↔ MvPowerSeries.constantCoeff g ∈ maximalIdeal O := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

theorem UpperTheory.V.CA.cl_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → ∀ (σ : Type) [Finite σ] (a : σ → R), (∀ s, a s ∈ maximalIdeal R) → maximalIdeal R ≤ (Ideal.span (Set.range a) ⊔ (maximalIdeal O).map (algebraMap O R)).radical → ∃ φ : MvPowerSeries σ O →ₐ[O] R, (∀ s, φ (MvPowerSeries.X s) = a s) ∧ φ.toRingHom.Finite ∧ IsLocalHom φ := by
  intro O _ _ _ _ R _ _ _ hR σ _ a ha hrad
  haveI := hR.noeth
  haveI := hR.complete
  haveI := hR.isLocalHom
  let φ : MvPowerSeries σ O →ₐ[O] R := GlobalTheory.mvEvalAdic O (maximalIdeal R) a ha
  have hX : ∀ s, φ (MvPowerSeries.X s) = a s := GlobalTheory.mvEvalAdic_X _ a ha
  have hXm : ∀ s, φ (MvPowerSeries.X s) ∈ maximalIdeal R := fun s => (hX s).symm ▸ ha s
  refine ⟨φ, hX, ?_, ?_⟩
  · letI : Algebra (MvPowerSeries σ O) R := φ.toRingHom.toAlgebra
    show Module.Finite (MvPowerSeries σ O) R
    haveI hOO : IsCO O O := ⟨inferInstance, ⟨fun x hx => by simpa using hx⟩, fun x => ⟨x, by simp⟩⟩
    haveI hCO := co_mvps O O σ
    haveI := hCO.complete
    haveI : IsScalarTower O (MvPowerSeries σ O) R :=
      IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    have hJ : Ideal.span (Set.range a) ⊔ (maximalIdeal O).map (algebraMap O R) ≤
        (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R) := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        rw [← hX s]
        refine Ideal.mem_map_of_mem (algebraMap (MvPowerSeries σ O) R) ?_
        rw [cl_mvps_max]
        simp
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        rw [Ideal.mem_comap, ← φ.commutes c]
        refine Ideal.mem_map_of_mem (algebraMap (MvPowerSeries σ O) R) ?_
        rw [cl_mvps_max, MvPowerSeries.algebraMap_apply]
        simpa using hc
    have hJm : (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R) ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap]
      rw [cl_mvps_max] at hg
      have h1 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => ((IsLocalRing.mem_maximalIdeal _).mp hg) (isUnit_of_map_unit (algebraMap O R) _ hu)
      have h2 := GlobalTheory.algHom_sub_constantCoeff_mem φ (K := maximalIdeal R) hXm g
      have h3 := Ideal.add_mem _ h2 h1
      have h4 : φ g ∈ maximalIdeal R := by simpa using h3
      exact h4
    haveI : IsHausdorff ((maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R)) R :=
      IsHausdorff.of_isLocalRing _ R (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (hrad.trans (Ideal.radical_mono hJ)) (IsNoetherian.noetherian (maximalIdeal R))
    haveI : Module.Finite O (R ⧸ maximalIdeal R) := hR.res_fin
    haveI : Module.Finite (MvPowerSeries σ O) (R ⧸ maximalIdeal R) :=
      Module.Finite.of_restrictScalars_finite O _ _
    haveI : Module.Finite (MvPowerSeries σ O)
        (R ⧸ (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R)) :=
      cl_mvps_fin (A := MvPowerSeries σ O) inferInstance hN
    exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal (MvPowerSeries σ O))
  · constructor
    intro g hg
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    by_contra hc
    have h1 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hc (isUnit_of_map_unit (algebraMap O R) _ hu)
    have h2 := GlobalTheory.algHom_sub_constantCoeff_mem φ (K := maximalIdeal R) hXm g
    have h3 : φ g ∈ maximalIdeal R := by simpa using Ideal.add_mem _ h2 h1
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) hg
