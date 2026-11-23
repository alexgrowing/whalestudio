import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

open GlobalTheory.K4

theorem UpperTheory.exists_isLocallyConstant_lift_to_geometric_galois :
    ∀ {F K Kb Z : Type} [Field F] [Field K] [Field Kb] [Algebra F K] [Algebra F Kb] [Algebra K Kb] [IsScalarTower F K Kb] [Algebra.IsAlgebraic F Kb] [Zero Z] (η₀ : (Kb ≃ₐ[K] Kb) → Z), IsLocallyConstant η₀ → ∃ η : (Kb ≃ₐ[F] Kb) → Z, IsLocallyConstant (fun g : geo F K Kb => η g) ∧ ∀ (g : Kb ≃ₐ[F] Kb) (g' : Kb ≃ₐ[K] Kb), g ∈ geo F K Kb → (∀ z, g' z = g z) → η g = η₀ g' := by
  classical
  intro F K Kb Z _ _ _ _ _ _ _ _ _ η₀ hη₀
  have key : ∀ g : Kb ≃ₐ[F] Kb, g ∈ geo F K Kb → ∀ k : K,
      g (algebraMap K Kb k) = algebraMap K Kb k := by
    intro g hg k
    have hg' : g ∈ (IsScalarTower.toAlgHom F K Kb).fieldRange.fixingSubgroup := hg
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' _
      (AlgHom.mem_fieldRange.2 ⟨k, rfl⟩)
  let r : geo F K Kb →* (Kb ≃ₐ[K] Kb) :=
    { toFun := fun g => AlgEquiv.ofRingEquiv (f := (g : Kb ≃ₐ[F] Kb).toRingEquiv) (key g g.2)
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have hr : ∀ g x, r g x = (g : Kb ≃ₐ[F] Kb) x := fun _ _ => rfl
  have hrc : Continuous r := by
    apply continuous_of_continuousAt_one r
    intro U hU
    rw [map_one] at hU
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Kb U).1 hU
    let b := Module.finBasis K E
    let S : Set Kb := Set.range (fun i => (b i : Kb))
    haveI : Finite S := Set.finite_range _
    haveI hE' : FiniteDimensional F (IntermediateField.adjoin F S) :=
      IntermediateField.finiteDimensional_adjoin
        (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
    rw [Filter.mem_map, mem_nhds_subtype]
    refine ⟨((IntermediateField.adjoin F S).fixingSubgroup : Set (Kb ≃ₐ[F] Kb)),
      (krullTopology_mem_nhds_one_iff F Kb _).2 ⟨_, hE', subset_rfl⟩, ?_⟩
    intro g hg
    apply hEU
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hlin : (r g).toLinearMap ∘ₗ E.val.toLinearMap = E.val.toLinearMap := by
      refine b.ext (fun i => ?_)
      show r g (b i : Kb) = (b i : Kb)
      rw [hr]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        (IntermediateField.subset_adjoin F S ⟨i, rfl⟩)
    exact congrArg (fun f => f ⟨x, hx⟩) hlin
  refine ⟨fun g => if h : g ∈ geo F K Kb then η₀ (r ⟨g, h⟩) else 0, ?_, ?_⟩
  · have : (fun g : geo F K Kb => (fun g => if h : g ∈ geo F K Kb then η₀ (r ⟨g, h⟩) else 0)
        (g : Kb ≃ₐ[F] Kb)) = η₀ ∘ r := by
      funext g
      simp [g.2]
    rw [this]
    exact hη₀.comp_continuous hrc
  · intro g g' hg hgg'
    simp only [hg, dif_pos]
    congr 1
    ext z
    rw [hr]
    exact (hgg' z).symm
