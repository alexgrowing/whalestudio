import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ComplDefY

open UpperTheory.Lit.CharWD GlobalTheory.Published

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.W

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {w : Plc F}

private theorem eo_lt (j : Emb l w) (x : 𝓞 F) (hx : x ∈ w.asIdeal) : ‖j.1 (algebraMap F _ (x : F))‖ < 1 := by
  have h1 : ‖algebraMap F (w.adicCompletion F) (x : F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem (K := F) (v := w) x).2 hx
    exact this
  have h2 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1
  have h3 := ((j.2.tendsto 0).comp h2)
  rw [map_zero] at h3
  have h4 : Filter.Tendsto (fun n : ℕ => ‖j.1 (algebraMap F _ (x : F))‖ ^ n) Filter.atTop (nhds 0) := by
    have := h3.norm
    simpa [Function.comp_def, map_pow, norm_pow] using this
  have := tendsto_pow_atTop_nhds_zero_iff.1 h4
  simpa [abs_of_nonneg (norm_nonneg _)] using this

private theorem eo_over (j : Emb l w) : w.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  have hmax : (w.asIdeal.under ℤ).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal w.asIdeal
  have hle : w.asIdeal.under ℤ ≤ Ideal.span {(l : ℤ)} := by
    intro n hn
    rw [Ideal.mem_span_singleton]
    have hmem : (algebraMap ℤ (𝓞 F) n) ∈ w.asIdeal := hn
    have h := eo_lt j _ hmem
    have e : j.1 (algebraMap F _ ((algebraMap ℤ (𝓞 F) n : 𝓞 F) : F)) = ((n : ℚ_[l]) : PadicAlgCl l) := by
      simp
    rw [e, PadicAlgCl.norm_extends] at h
    rw [← PadicInt.norm_int_lt_one_iff_dvd]
    simpa [PadicInt.norm_def] using h
  have hne : Ideal.span {(l : ℤ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun hu => (Fact.out : l.Prime).ne_one (by simpa using Int.isUnit_iff_natAbs_eq.1 hu)
  exact ⟨(hmax.eq_of_le hne hle).symm⟩

private theorem eo_comp (j : Emb l w) (φ : ℚ_[l] →+* w.adicCompletion F) (hφ : Continuous φ) (x : ℚ_[l]) :
    j.1 (φ x) = algebraMap ℚ_[l] (Qbar l) x := by
  have h1 : Continuous fun y : ℚ_[l] => j.1 (φ y) := j.2.comp hφ
  have h2 : Continuous (algebraMap ℚ_[l] (Qbar l)) := continuous_algebraMap ℚ_[l] (Qbar l)
  have key : (fun y => j.1 (φ y)) = algebraMap ℚ_[l] (Qbar l) := by
    refine (Padic.denseRange_ratCast l).equalizer h1 h2 ?_
    funext q
    simp
  exact congrFun key x

private theorem eo_abs {k K Ω : Type} [Field k] [Field K] [Field Ω] [CharZero K] [Algebra k K] [Algebra k Ω]
    [IsAlgClosure k Ω] (τ₀ : K →ₐ[k] Ω) :
    (∀ τ : K →ₐ[k] Ω, ∃ s : Ω ≃ₐ[k] Ω, ∀ x, τ x = s (τ₀ x)) ∧
    ∀ y : Ω, (∀ s : Ω ≃ₐ[k] Ω, (∀ x, τ₀ x = s (τ₀ x)) → y = s y) → ∃ u, y = τ₀ u := by
  haveI : CharZero k := (algebraMap k K).charZero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  haveI : Normal k Ω := inferInstance
  haveI : IsGalois k Ω := inferInstance
  constructor
  · intro τ
    letI : Algebra K Ω := τ₀.toRingHom.toAlgebra
    haveI : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun r => (τ₀.commutes r).symm)
    let g := τ.liftNormal Ω
    refine ⟨AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g), fun x => ?_⟩
    have := τ.liftNormal_commutes Ω x
    exact this.symm
  · intro y hy
    have hmem : y ∈ IntermediateField.fixedField τ₀.fieldRange.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      rw [IntermediateField.mem_fixingSubgroup_iff] at hf
      exact (hy f (fun x => (hf _ ⟨x, rfl⟩).symm)).symm
    rw [InfiniteGalois.fixedField_fixingSubgroup, AlgHom.mem_fieldRange] at hmem
    obtain ⟨u, hu⟩ := hmem
    exact ⟨u, hu.symm⟩

end SlopeTestRemainingChoices

theorem UpperTheory.Lit.CharWD.embOrbit :
    EmbOrbit := by
  intro F _ _ l _ w c hc hne
  obtain ⟨τ₀⟩ := hne
  haveI := eo_over τ₀
  obtain ⟨f, φ, -, hφc, -, -, -⟩ := KStar.Ram.existsUnique_padic_hom w l
  letI : Algebra ℚ_[l] (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) := φ.toAlgebra
  have toAlg : ∀ τ : UpperTheory.V.W.Emb l w,
      ∃ t : IsDedekindDomain.HeightOneSpectrum.adicCompletion F w →ₐ[ℚ_[l]] Formalism.ConjugateSelfDual.Qbar l,
        ∀ x, t x = τ.1 x :=
    fun τ => ⟨AlgHom.mk τ.1 (fun r => eo_comp τ φ hφc r), fun _ => rfl⟩
  haveI : CharZero (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) :=
    charZero_of_injective_algebraMap
      (algebraMap F (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w)).injective
  obtain ⟨t₀, ht₀⟩ := toAlg τ₀
  obtain ⟨hext, hfix⟩ := eo_abs t₀
  obtain ⟨u, hu⟩ := hfix (c τ₀) (fun s hs => hc s τ₀ τ₀ (fun x => by
    have h := hs x
    rwa [ht₀] at h))
  refine ⟨u, fun τ => ?_⟩
  obtain ⟨t, ht⟩ := toAlg τ
  obtain ⟨s, hs⟩ := hext t
  have h := hc s τ₀ τ (fun x => by
    have h' := hs x
    rwa [ht, ht₀] at h')
  rw [h, hu, ← hs u, ht]
