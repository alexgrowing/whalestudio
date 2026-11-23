import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem continuous_of_right_invariant_open_subgroup {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_mul_left g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht (hH.mem_nhds H.one_mem)] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem UpperTheory.V.Ws.exists_descent_to_galoisGroupUnramifiedOutside :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N : ℕ), (∀ v, v ∈ plDvd F N → v ∈ S) → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → IsOpen (K : Set (G F Ω)) → (∀ σ ∈ K, ∀ m, ρ σ m = m) → ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, (∀ g m, ρS (toGS Ω _ g) m = ρ g m) ∧ ContAction ρS ∧ ∀ z ∈ cocOff ρ (ineOff F Ω N), ∃ y ∈ Z1 ρS, ∀ g, y (toGS Ω _ g) = z g := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ S ρ K N hS hine hK hKρ
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ (S : Set (HeightOneSpectrum (𝓞 F))) →
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Inertia A, σ ∈ ineOff F Ω N := by
    intro v hv A hA σ hσ
    refine ⟨A, ?_, hσ⟩
    intro hlt
    apply hv
    apply hS
    have h1 := (hA (N : 𝓞 F)).1
    simp only [plDvd, Set.mem_setOf_eq]
    apply h1
    simpa using hlt
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    have hker : ∀ g, g ∈ ρ.ker ↔ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    have hopen : IsOpen (ρ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      apply Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      intro σ hσ
      exact (hker σ).2 (hKρ σ hσ)
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    exact (hker σ).2 (hine σ (hN v hv A hA σ hσ))
  let ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    QuotientGroup.lift _ ρ hNS
  have hρS : ∀ g m, ρS (toGS Ω _ g) m = ρ g m := by
    intro g m
    rfl
  refine ⟨ρS, hρS, ?_, ?_⟩
  · show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => ρS p.1 p.2
    rw [continuous_prod_of_discrete_right]
    intro m
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    apply continuous_of_right_invariant_open_subgroup K hK
    intro g h hh
    show ρ (g * h) m = ρ g m
    rw [map_mul, Module.End.mul_apply, hKρ h hh]
  · intro z hz
    obtain ⟨hzlc, hzc, hz0⟩ := hz
    have hz1 : z 1 = 0 := by
      have := hzc 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at this
      simpa using this
    let φ : G F Ω →* Function.End M :=
      { toFun := fun g m => ρ g m + z g
        map_one' := by
          funext m
          show ρ 1 m + z 1 = m
          rw [hz1, map_one]
          simp
        map_mul' := by
          intro g h
          funext m
          show ρ (g * h) m + z (g * h) = ρ g (ρ h m + z h) + z g
          rw [hzc, map_mul, Module.End.mul_apply, map_add]
          abel }
    have hkerφ : ∀ g, g ∈ φ.ker ↔ z g = 0 ∧ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h' : ∀ m, ρ g m + z g = m := fun m => congrFun h m
        have h0 : z g = 0 := by simpa using h' 0
        refine ⟨h0, fun m => ?_⟩
        simpa [h0] using h' m
      · rintro ⟨h0, h1⟩
        funext m
        show ρ g m + z g = m
        rw [h0, h1, add_zero]
    have hopen : IsOpen (φ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      have hU : z ⁻¹' {0} ∈ nhds (1 : G F Ω) :=
        (hzlc.isOpen_fiber 0).mem_nhds (by simpa using hz1)
      apply Filter.mem_of_superset (Filter.inter_mem (hK.mem_nhds K.one_mem) hU)
      rintro σ ⟨hσK, hσz⟩
      exact (hkerφ σ).2 ⟨hσz, hKρ σ hσK⟩
    have hNSφ : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ φ.ker := by
      apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
      apply Subgroup.normalClosure_le_normal
      intro σ hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨v, hv, A, hA, hσ⟩ := hσ
      have hm := hN v hv A hA σ hσ
      exact (hkerφ σ).2 ⟨hz0 σ hm, hine σ hm⟩
    let φS := QuotientGroup.lift _ φ hNSφ
    let y : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := fun q => φS q 0
    have hy : ∀ g, y (toGS Ω _ g) = z g := by
      intro g
      show ρ g 0 + z g = z g
      simp
    refine ⟨y, ⟨?_, ?_⟩, hy⟩
    · rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      have : (y ∘ QuotientGroup.mk) = z := funext hy
      rw [this]
      exact hzlc.continuous
    · intro q₁ q₂
      induction q₁ using QuotientGroup.induction_on with
      | H g =>
        induction q₂ using QuotientGroup.induction_on with
        | H h =>
          have e := hy (g * h)
          rw [map_mul] at e
          show y (toGS Ω _ g * toGS Ω _ h) = y (toGS Ω _ g) + ρS (toGS Ω _ g) (y (toGS Ω _ h))
          rw [e, hy, hy, hρS, hzc]
