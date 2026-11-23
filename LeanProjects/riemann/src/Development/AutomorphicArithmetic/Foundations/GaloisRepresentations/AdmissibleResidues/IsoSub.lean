import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PiPtsHecke

open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Hi

private theorem irreducible_subrep_isotypic {H Y V : Type} {I : Type 1} {S : I → Type} [Group H] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    (σ : ∀ i, Representation ℂ H (S i)) (hσ : ∀ i, (σ i).IsIrreducible)
    (π : Representation ℂ H Y) (ρ : Representation ℂ H V) (j : Y →ₗ[ℂ] V) (hj : Function.Injective j)
    (he : ∀ g y, j (π g y) = ρ g (j y))
    (h : ∀ y, j y ∈ ⨆ (i : I) (f : {f : S i →ₗ[ℂ] V // ∀ g v, f (σ i g v) = ρ g (f v)}), LinearMap.range f.1)
    (y : Y) :
    y ∈ ⨆ (i : I) (f : {f : S i →ₗ[ℂ] Y // ∀ g v, f (σ i g v) = π g (f v)}), LinearMap.range f.1 := by
  let R := MonoidAlgebra ℂ H
  haveI hsim : ∀ i, IsSimpleModule R (σ i).asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule (σ i)).mp (hσ i)
  let J : π.asModule →ₗ[R] ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule π ρ ⟨j, fun g => LinearMap.ext (he g)⟩
  let s : Set (Submodule R ρ.asModule) := {m | ∃ i, Nonempty (m ≃ₗ[R] (σ i).asModule)}
  haveI hs : ∀ m : s, IsSimpleModule R m := by
    rintro ⟨m, i, ⟨e⟩⟩
    exact IsSimpleModule.congr e
  have h1 : ∀ v ∈ ⨆ (i : I) (f : {f : S i →ₗ[ℂ] V // ∀ g v, f (σ i g v) = ρ g (f v)}), LinearMap.range f.1,
      ρ.asModuleEquiv.symm v ∈ sSup s := by
    intro v hv
    refine Submodule.iSup_induction _ (motive := fun z => ρ.asModuleEquiv.symm z ∈ sSup s) hv ?_ ?_ ?_
    · intro i v hv
      refine Submodule.iSup_induction _ (motive := fun z => ρ.asModuleEquiv.symm z ∈ sSup s) hv ?_ ?_ ?_
      · rintro f _ ⟨t, rfl⟩
        let F : (σ i).asModule →ₗ[R] ρ.asModule :=
          Representation.IntertwiningMap.equivLinearMapAsModule (σ i) ρ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
        have : LinearMap.range F ≤ sSup s := by
          rcases LinearMap.injective_or_eq_zero F with hi | hz
          · exact le_sSup ⟨i, ⟨(LinearEquiv.ofInjective _ hi).symm⟩⟩
          · rw [hz, LinearMap.range_zero]; exact bot_le
        exact this ⟨(σ i).asModuleEquiv.symm t, rfl⟩
      · rw [map_zero]; exact zero_mem _
      · intro a b ha hb
        rw [map_add]; exact add_mem ha hb
    · rw [map_zero]; exact zero_mem _
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb
  have hJ : ∀ x, J x ∈ sSup s := fun x => h1 _ (h (π.asModuleEquiv x))
  have hJi : Function.Injective J := hj
  haveI : IsSemisimpleModule R (sSup s : Submodule R ρ.asModule) := by
    rw [sSup_eq_iSup]
    exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm =>
      haveI := hs ⟨m, hm⟩
      inferInstance
  let J' : π.asModule →ₗ[R] (sSup s : Submodule R ρ.asModule) := J.codRestrict _ hJ
  have hJ' : Function.Injective J' := fun a b hab => hJi (congrArg Subtype.val hab)
  haveI : IsSemisimpleModule R π.asModule := IsSemisimpleModule.of_injective J' hJ'
  have h3 : π.asModuleEquiv.symm y ∈ sSup {m : Submodule R π.asModule | IsSimpleModule R m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]; trivial
  rw [sSup_eq_iSup'] at h3
  rw [← π.asModuleEquiv.apply_symm_apply y]
  refine Submodule.iSup_induction _ (motive := fun z => π.asModuleEquiv z ∈ _) h3 ?_ ?_ ?_
  · rintro ⟨m, hm⟩ z hz
    haveI : IsSimpleModule R m := hm
    let e0 : m ≃ₗ[R] m.map J := Submodule.equivMapOfInjective J hJi m
    haveI : IsSimpleModule R (m.map J) := IsSimpleModule.congr e0.symm
    have hle : m.map J ≤ sSup s := by
      rintro _ ⟨x, -, rfl⟩
      exact hJ x
    obtain ⟨n, ⟨i, ⟨e2⟩⟩, ⟨e1⟩⟩ := (m.map J).linearEquiv_of_le_sSup s hle
    let e : m ≃ₗ[R] (σ i).asModule := (e0.trans e1).trans e2
    let F := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i) π).symm (m.subtype ∘ₗ e.symm.toLinearMap)
    refine Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem ⟨F.toLinearMap, F.isIntertwining⟩ ⟨(σ i).asModuleEquiv (e ⟨z, hz⟩), ?_⟩)
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
  · rw [map_zero]; exact zero_mem _
  · intro a b ha hb
    rw [map_add]; exact add_mem ha hb

theorem UpperTheory.GalN.V.isoSub :
    ∀ (H Y V : Type) (I : Type 1) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup V] [Module ℂ V] (σ : I → SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H V) (j : Y →ₗ[ℂ] V), Function.Injective j → (∀ g y, j (π g y) = ρ g (j y)) → (∀ y, j y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] V // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1) → ∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1 := by
  intro H Y V I _ _ _ _ _ _ _ σ π ρ j hj he h y
  exact irreducible_subrep_isotypic (fun i => (σ i).ρ) (fun i => (σ i).irred) π ρ j hj he h y
