import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.z1fMap :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (φ : G →* GQ l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), (ContAction ρ → ReciprocityTheory.Gal.B1 ρ ≤ UpperTheory.V.Loc.finiteCocycles φ ρ) ∧ ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ, (fun g => f (c g)) ∈ UpperTheory.V.Loc.finiteCocycles φ ρ' := by
  intro l _ G _ _ φ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ'
  refine ⟨fun hρ => ?_, fun f hf c hc => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[ℚ_[l]] (1 : Bcr l), fun g => ?_⟩
    · have h1 : Continuous fun g : G => ρ g v :=
        Continuous.comp (g := fun p : G × V => ρ p.1 p.2) (f := fun g : G => (g, v)) hρ (by fun_prop)
      exact h1.sub continuous_const
    · simp [ReciprocityTheory.Gal.d0]
    · simp [ReciprocityTheory.Gal.d0, actC, sub_tmul]
  · obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
    have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
    · simp only [hcc g h, map_add, hf]
    · have key : ∀ y : V ⊗[ℚ_[l]] Bcr l, LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
          actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [actC, hf]
        | add a b ha hb => simp only [map_add, ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
