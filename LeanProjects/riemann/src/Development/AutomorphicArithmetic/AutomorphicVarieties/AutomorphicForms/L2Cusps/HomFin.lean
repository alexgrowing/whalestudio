import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import GroundTheory.AutomorphicForms.TensorProductTheorem.KProjApplyEqSelfIff

open GroundTheory.Automorphic

private theorem UpperTheory.V.KernelIndexFullLattice.homFin_comp {R B S : Type} [Ring R] [AddCommGroup B] [Module R B]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    isotypicComponent R B S = ⊥ ∨ isotypicComponent R B S ∈ isotypicComponents R B := by
  by_cases h : isotypicComponent R B S = ⊥
  · exact Or.inl h
  · right
    obtain ⟨m, ⟨e⟩, -⟩ : ∃ m ∈ {m : Submodule R B | Nonempty (m ≃ₗ[R] S)}, m ≠ ⊥ := by
      by_contra hc
      push_neg at hc
      exact h (sSup_eq_bot.mpr hc)
    haveI : IsSimpleModule R m := IsSimpleModule.congr e
    exact ⟨m, inferInstance, e.isotypicComponent_eq.symm⟩

theorem UpperTheory.V.KernelIndexFullLattice.homFin_holds :
    UpperTheory.V.KernelIndexFullLattice.HomFin := by
  intro C M X _ _ _ _ _ _ _ _ _ _ σ hσ τ hτ F hF
  have hτK : CompactRep.IsKFinite τ := ⟨fun _ => inferInstance, hτ⟩
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ C) τ.asModule := CompactRep.isSemisimpleModule_asModule hτK
  haveI : IsNoetherian ℂ τ.asModule := inferInstanceAs (IsNoetherian ℂ X)
  haveI hτT : IsScalarTower ℂ (MonoidAlgebra ℂ C) τ.asModule := by
    refine ⟨fun c a v => ?_⟩
    show τ.asAlgebraHom (c • a) _ = c • τ.asAlgebraHom a _
    rw [map_smul]
    rfl
  haveI hσT : IsScalarTower ℂ (MonoidAlgebra ℂ C) σ.asModule := by
    refine ⟨fun c a v => ?_⟩
    show σ.asAlgebraHom (c • a) _ = c • σ.asAlgebraHom a _
    rw [map_smul]
    rfl
  haveI : IsNoetherian (MonoidAlgebra ℂ C) τ.asModule := isNoetherian_of_tower ℂ inferInstance
  obtain ⟨t, ht, htop⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact
    (Submodule (MonoidAlgebra ℂ C) τ.asModule) {m | IsSimpleModule (MonoidAlgebra ℂ C) m}
  rw [IsSemisimpleModule.sSup_simples_eq_top] at htop
  let W : Submodule (MonoidAlgebra ℂ C) τ.asModule → Submodule ℂ M := fun m =>
    F ⊓ ((isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m).restrictScalars ℂ : Submodule ℂ σ.asModule)
  refine ⟨t.sup W, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun N : Submodule ℂ M => FiniteDimensional ℂ N) ?_ ?_ ?_
    · exact inferInstance
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
    · intro m hm
      haveI : IsSimpleModule (MonoidAlgebra ℂ C) m := ht hm
      rcases UpperTheory.V.KernelIndexFullLattice.homFin_comp (R := MonoidAlgebra ℂ C) (B := σ.asModule) (S := m) with h | hc
      · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
        intro v hv
        have hv2 : (show σ.asModule from v) ∈ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m := hv.2
        rw [h] at hv2
        have hv0 : (show σ.asModule from v) = 0 := (Submodule.mem_bot (MonoidAlgebra ℂ C)).1 hv2
        exact (Submodule.mem_bot ℂ).2 hv0
      · haveI := hF _ hc
        refine Submodule.finiteDimensional_of_le
          (S₂ := LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype)) ?_
        intro v hv
        exact ⟨⟨v, hv.1⟩, (CompactRep.kProj_apply_eq_self_iff hσ hc).2 hv.2⟩
  · intro f hf hFf x
    let f' : τ.asModule →ₗ[ℂ] σ.asModule :=
      σ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ τ.asModuleEquiv.toLinearMap
    let g : τ.asModule →ₗ[MonoidAlgebra ℂ C] σ.asModule :=
      MonoidAlgebra.equivariantOfLinearOfComm f'
        (fun k v => by
          simp [f']
          exact hf k v)
    have hg : ∀ y : τ.asModule, g y = f y := fun y => rfl
    have one : ∀ m ∈ t, ∀ y ∈ m, g y ∈ t.sup W := by
      intro m hm y hy
      haveI : IsSimpleModule (MonoidAlgebra ℂ C) m := ht hm
      refine Finset.le_sup (f := W) hm ⟨?_, ?_⟩
      · rw [hg]
        exact hFf y
      show g y ∈ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m
      rcases (g.domRestrict m).injective_or_eq_zero with hi | h0
      · have hle : LinearMap.range (g.domRestrict m) ≤ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m :=
          le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
        exact hle ⟨⟨y, hy⟩, rfl⟩
      · have h1 : g y = 0 := by simpa using LinearMap.congr_fun h0 ⟨y, hy⟩
        rw [h1]
        exact zero_mem _
    have key : ∀ s : Finset (Submodule (MonoidAlgebra ℂ C) τ.asModule), s ⊆ t →
        ∀ y ∈ s.sup id, g y ∈ t.sup W := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _ y hy
        have hy0 : y = 0 := by simpa using hy
        rw [hy0, map_zero]
        exact zero_mem _
      | insert a s ha ih =>
        intro hs y hy
        rw [Finset.sup_insert] at hy
        obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add]
        exact add_mem (one a (hs (Finset.mem_insert_self a s)) y1 hy1)
          (ih ((Finset.subset_insert a s).trans hs) y2 hy2)
    have hx : (show τ.asModule from x) ∈ t.sup id := htop ▸ Submodule.mem_top
    have := key t subset_rfl _ hx
    rw [hg] at this
    exact this
