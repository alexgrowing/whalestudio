import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GenDec

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem toZMod_cycZ_eq_one_of_cycMod_eq_one (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
    (g : G F Ω) (h : cycMod F Ω l 1 g = 1) :
    PadicInt.toZMod ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have h1 := congrArg Units.val h
  simp only [cycMod, MonoidHom.comp_apply, Units.coe_map, Units.val_one] at h1
  have hk : ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
      RingHom.ker (PadicInt.toZModPow 1 : ℤ_[l] →+* ZMod (l ^ 1)) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    exact h1
  rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hk
  exact hk

theorem UpperTheory.V.GC.gen :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → (∀ v, ∃ s, Φ.om k (Φ.loc v s) ≠ 1) → ∀ v, ∃ (u : Fin (Φ.dv v) → Φ.Gv v) (a₀ : Fin (Φ.dv v)), (∀ a, u a ∈ Φ.Iv v ∧ Φ.Ψ (Φ.loc v (u a)) = 1) ∧ (∀ a, a ≠ a₀ → u a ∈ Φ.Nv v) ∧
    ∀ (B : Type) [CommGroup B] [Finite B], IsPGroup l B → ∀ χ : Φ.Gv v →* B, IsOpen (χ.ker : Set (Φ.Gv v)) → (∀ a, χ (u a) = 1) → ∀ g ∈ Φ.Iv v, χ g = 1 := by
  intro hP F Ω _ _ _ _ _ l _ k _ _ Φ S K π ι A pl e c hL hom v
  have hdv : Φ.dv v = locDeg (pl v) := hL.dv v
  have hmemv : ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal := (hL.loc.mem (pl v)).1 ⟨v, rfl⟩
  have hcyc : ∃ g ∈ Dec (A v), cycMod F Ω l 1 g ≠ 1 := by
    obtain ⟨s, hs⟩ := hom v
    refine ⟨ι v s, ?_, fun h1 => hs ?_⟩
    · rw [← hL.loc.range v]
      exact ⟨s, rfl⟩
    · have h2 := toZMod_cycZ_eq_one_of_cycMod_eq_one F Ω l _ h1
      apply Units.ext
      simp [Fr.Frame.om, hL.loc_eq, hL.eps, h2]
  obtain ⟨u', a₀', hu1, hu2, hu3⟩ := genDec hP.lf hP.lt hP.le F Ω l hL.g.odd (pl v) (A v)
    (hL.loc.isOver v) hmemv hcyc K hL.g.normal hL.g.isOpen hL.g.idx
  let eq : Φ.Gv v ≃* Dec (A v) :=
    (MonoidHom.ofInjective (hL.loc.ι_inj v)).trans (MulEquiv.subgroupCongr (hL.loc.range v))
  have heq : ∀ x, ((eq x : Dec (A v)) : G F Ω) = ι v x := fun x => rfl
  have hcont : Continuous eq := by
    apply continuous_induced_rng.2
    exact hL.loc.cont v
  let h' := hcont.homeoOfEquivCompactToT2 (f := eq.toEquiv)
  refine ⟨fun a => eq.symm (u' (Fin.cast hdv a)), Fin.cast hdv.symm a₀', fun a => ⟨?_, ?_⟩,
    fun a ha => ?_, ?_⟩
  · rw [hL.ine v, Subgroup.mem_comap, ← heq, MulEquiv.apply_symm_apply]
    exact (hu1 _).1
  · rw [hL.loc_eq, ← heq, MulEquiv.apply_symm_apply]
    exact hL.K_Ψ _ (hu1 _).2
  · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hL.ine v, Subgroup.mem_comap, ← heq, MulEquiv.apply_symm_apply]
      exact (hu1 _).1
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hL.loc_eq, hL.eps, ← heq,
        MulEquiv.apply_symm_apply]
      refine hu2 _ fun h => ha ?_
      rw [← h]
      ext
      simp
  · intro B _ _ hB χ hχ hu g hg
    let χ' : Dec (A v) →* B := χ.comp eq.symm.toMonoidHom
    have hopen : IsOpen (SetLike.coe χ'.ker) := by
      have hs : SetLike.coe χ'.ker = h'.symm ⁻¹' (SetLike.coe χ.ker) := rfl
      rw [hs]
      exact hχ.preimage h'.symm.continuous
    have hg' : ((eq g : Dec (A v)) : G F Ω) ∈ Ine (A v) := by
      rw [heq]
      rw [hL.ine v] at hg
      exact hg
    have := hu3 B hB χ' hopen (fun a => by simpa [χ'] using hu (Fin.cast hdv.symm a)) (eq g) hg'
    simpa [χ'] using this
