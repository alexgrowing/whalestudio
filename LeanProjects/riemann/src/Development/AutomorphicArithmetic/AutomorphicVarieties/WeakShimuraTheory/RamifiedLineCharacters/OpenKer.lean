import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GysCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MapRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem val_nat {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  have h1 := h ((n : ℕ) : 𝓞 F)
  have e : algebraMap F Ω (((n : ℕ) : 𝓞 F) : F) = (n : Ω) := by simp
  rw [e] at h1
  exact h1

private theorem fin_over (F : Type) [Field F] [NumberField F] (U : Finset ℕ) (hU : ∀ p ∈ U, p ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∈ S ↔ ∃ p ∈ U, (p : 𝓞 F) ∈ v.asIdeal := by
  have h : {v : HeightOneSpectrum (𝓞 F) | ∃ p ∈ U, (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h1 : ∀ p ∈ (U : Set ℕ), {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
      intro p hp
      have h0 : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hU p hp
      refine (Ideal.finite_factors h0).subset fun v hv => ?_
      exact Ideal.dvd_span_singleton.2 hv
    refine (Set.Finite.biUnion U.finite_toSet h1).subset fun v hv => ?_
    obtain ⟨p, hp, hv⟩ := hv
    exact Set.mem_biUnion hp hv
  exact ⟨h.toFinset, fun v => h.mem_toFinset⟩

private theorem open_cyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] :
    IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) :=
  (isOpen_discrete {(1 : (ZMod (l ^ 1))ˣ)}).preimage GlobalTheory.Published.PoitouTate.continuous_cycMod

private theorem open_ker {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (h : ContAction ρ) :
    IsOpen ((MonoidHom.ker ρ : Subgroup Γ) : Set Γ) := by
  have e : ((MonoidHom.ker ρ : Subgroup Γ) : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
    ext g
    simp [MonoidHom.mem_ker, LinearMap.ext_iff]
  rw [e]
  exact isOpen_iInter_of_finite fun m =>
    (isOpen_discrete _).preimage (Continuous.comp h (continuous_id.prodMk continuous_const))

theorem UpperTheory.V.Ws.Gys.gysT :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → (T.fr W).Gys l (T.Next W) := by
  intro hP Ω _ _ _ l hl c D T hD W hW M _ _ _ _ _ ρ hρ hN m0 hm0
  classical
  obtain ⟨S₀, hS₀⟩ := fin_over T.F (D.S ∪ W) fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact (hD.S_prime p h).ne_zero
    · exact (hW p h).1.ne_zero
  have hl₀ : ∀ v : HeightOneSpectrum (𝓞 T.F), (l : 𝓞 T.F) ∈ v.asIdeal → v ∈ S₀ := fun v hv =>
    (hS₀ v).2 ⟨l, Finset.mem_union_left _ hD.l_mem, hv⟩
  have hunr : UnrOut ρ S₀ := by
    intro v hv A hA g hg
    have haw : Raw.Away (D.S ∪ W) A := fun p hp h => hv ((hS₀ v).2 ⟨p, hp, (val_nat hA p).1 h⟩)
    refine hN g ⟨A, fun p hp => haw p ?_, hg, UpperTheory.V.Ws.Gys.unrS D T hD A (fun p hp => haw p (Finset.mem_union_left _ hp)) g hg⟩
    rcases Finset.mem_insert.1 hp with rfl | h
    · exact Finset.mem_union_left _ hD.l_mem
    · exact Finset.mem_union_right _ h
  have hQ := UpperTheory.V.Ws.Gys.placesQ D T hD (MonoidHom.ker ρ ⊓ (cycMod T.F Ω l 1).ker)
    ((open_ker ρ hρ).inter (open_cyc T.F Ω l))
  obtain ⟨S, hS, z, hz, hloc, hg⟩ := UpperTheory.V.Ws.Gys.gysCore hP T.F Ω l M hD.l_odd ρ S₀ _ hρ hl₀ hunr hQ
    (fun v hv A hA g hg => hv.2 A hA hg) m0 hm0
  have hw : ∀ v ∈ S, v ∉ S₀ → ∃ w : ℕ, w.Prime ∧ T.Splits w ∧ (w : 𝓞 T.F) ∈ v.asIdeal := fun v hv hv' =>
    ((hS v hv).resolve_left hv').1
  choose! wf hwf using hw
  have hnext : T.Next W (T.fr (W ∪ (S \ S₀).image wf)).N := by
    refine ⟨_, Finset.subset_union_left, fun w h => ?_, rfl⟩
    rcases Finset.mem_union.1 h with h | h
    · exact hW w h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have := hwf v (Finset.mem_sdiff.1 hv).1 (Finset.mem_sdiff.1 hv).2
      exact ⟨this.1, this.2.1⟩
  refine ⟨_, hnext, z, hz.1, fun g hg => ?_, fun u => ?_, hg⟩
  · have h1 : ρ g = 1 := hN g (hnext.sub hg)
    obtain ⟨A, hA, hg, -⟩ := hg
    obtain ⟨p1, p2, -⟩ := UpperTheory.V.Base.places T.F Ω l A
    by_cases ht : A = ⊤
    · rw [(p2 ht).1, Subgroup.mem_bot] at hg
      subst hg
      have := hz.1.2 1 1
      simpa using this
    obtain ⟨v, hv⟩ := p1 ht
    by_cases hvS : v ∈ S
    · by_cases hv0 : v ∈ S₀
      · obtain ⟨m, hm⟩ := hloc v hv0 A hv
        rw [hm g (Ine_le_Dec A hg), h1]
        simp
      · refine absurd ((val_nat hv _).2 (hwf v hvS hv0).2.2) (hA _ ?_)
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_sdiff.2 ⟨hvS, hv0⟩)))
    · exact hz.2 v hvS A hv g hg
  · obtain ⟨p1, p2, -⟩ := UpperTheory.V.Base.places T.F Ω l (T.pl u)
    obtain ⟨v, hv⟩ := p1 fun ht => (p2 ht).2 (T.ovl u)
    exact hloc v (hl₀ v ((val_nat hv l).1 (T.ovl u))) _ hv
