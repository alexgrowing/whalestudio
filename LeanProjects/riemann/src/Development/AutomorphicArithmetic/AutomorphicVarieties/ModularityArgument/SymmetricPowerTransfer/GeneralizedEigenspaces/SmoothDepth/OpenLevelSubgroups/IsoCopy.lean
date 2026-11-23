import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem isoCopy_struct {H T M : Type} [Group H] [AddCommGroup T] [Module ℂ T] [AddCommGroup M] [Module ℂ M]
    (τ : Representation ℂ H T) (μ : Representation ℂ H M) (hτ : τ.IsIrreducible)
    (hsup : (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) = ⊤) :
    IsSemisimpleModule (MonoidAlgebra ℂ H) μ.asModule ∧
      IsIsotypicOfType (MonoidAlgebra ℂ H) μ.asModule τ.asModule := by
  have hS : IsSimpleModule (MonoidAlgebra ℂ H) τ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule τ).1 hτ
  let F : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)} →
      (τ.asModule →ₗ[MonoidAlgebra ℂ H] μ.asModule) := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule τ μ
      (f.1.intertwiningMap_of_isIntertwiningMap τ μ f.2)
  have hle : ∀ f, LinearMap.range (F f) ≤ isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule := by
    intro f
    rcases LinearMap.injective_or_eq_zero (F f) with hi | h0
    · exact le_sSup ⟨(LinearEquiv.ofInjective (F f) hi).symm⟩
    · simp [h0]
  have htop : isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : ∀ y : M, y ∈ (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) := fun y => by
      rw [hsup]; exact Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun y : M => (y : μ.asModule) ∈ isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule)
      (hx x) ?_ ?_ ?_
    · rintro f _ ⟨t, rfl⟩
      exact hle f ⟨t, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ H) (isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule) :=
    inferInstance
  rw [htop] at hss
  exact ⟨IsSemisimpleModule.congr (Submodule.topEquiv (R := MonoidAlgebra ℂ H) (M := μ.asModule)).symm,
    IsIsotypicOfType.of_isotypicComponent_eq_top htop⟩

theorem UpperTheory.V.Z.Sym.Al.isoCopy :
    ∀ (H T M : Type) [Group H] [AddCommGroup T] [Module ℂ T] [AddCommGroup M] [Module ℂ M] (τ : Representation ℂ H T) (μ : Representation ℂ H M),
        τ.IsIrreducible → (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) = ⊤ →
        (∀ v : M, v ≠ 0 → ∃ p : M →ₗ[ℂ] T, (∀ h x, p (μ h x) = τ h (p x)) ∧ p v ≠ 0) ∧
        ∀ (N I : Type) [AddCommGroup N] [Module ℂ N] [Finite I] (ν : Representation ℂ H N) (q : I → N →ₗ[ℂ] M),
          (∀ i h x, q i (ν h x) = μ h (q i x)) → (∀ x, (∀ i, q i x = 0) → x = 0) → Nontrivial N →
          ∃ f : T →ₗ[ℂ] N, f ≠ 0 ∧ ∀ h x, f (τ h x) = ν h (f x) := by
  intro H T M _ _ _ _ _ τ μ hτ hsup
  obtain ⟨hss, hiso⟩ := isoCopy_struct τ μ hτ hsup
  refine ⟨fun v hv => ?_, fun N I _ _ _ ν q hq hsep hN => ?_⟩
  · obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
    have hev : e (v : μ.asModule) ≠ 0 := fun h => hv (e.map_eq_zero_iff.1 h)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hev
    let P : μ.asModule →ₗ[MonoidAlgebra ℂ H] τ.asModule :=
      (Finsupp.lapply i).comp e.toLinearMap
    let p := (Representation.IntertwiningMap.equivLinearMapAsModule μ τ).symm P
    exact ⟨p.toLinearMap, fun h x => Representation.IntertwiningMap.isIntertwining _ _ p h x, hi⟩
  · let Q : I → (ν.asModule →ₗ[MonoidAlgebra ℂ H] μ.asModule) := fun i =>
      Representation.IntertwiningMap.equivLinearMapAsModule ν μ
        ((q i).intertwiningMap_of_isIntertwiningMap ν μ (hq i))
    have hinj : Function.Injective (LinearMap.pi Q) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      exact hsep x fun i => congrFun hx i
    have hNs : IsSemisimpleModule (MonoidAlgebra ℂ H) ν.asModule :=
      IsSemisimpleModule.of_injective _ hinj
    haveI : Nontrivial ν.asModule := hN
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule (MonoidAlgebra ℂ H) ν.asModule)
    rw [← isSimpleModule_iff_isAtom] at hS
    haveI := hS
    haveI := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) S
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    obtain ⟨i, hi⟩ : ∃ i, Q i s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hs (Subtype.ext (hsep s.1 fun i => hc i))
    have hne : (Q i).comp S.subtype ≠ 0 := fun h => hi (LinearMap.congr_fun h s)
    have hj : Function.Injective ((Q i).comp S.subtype) :=
      (LinearMap.injective_or_eq_zero _).resolve_right hne
    let e1 := LinearEquiv.ofInjective _ hj
    haveI : IsSimpleModule (MonoidAlgebra ℂ H) (LinearMap.range ((Q i).comp S.subtype)) := IsSimpleModule.congr e1.symm
    obtain ⟨e2⟩ := hiso (LinearMap.range ((Q i).comp S.subtype))
    let G : τ.asModule →ₗ[MonoidAlgebra ℂ H] ν.asModule :=
      S.subtype.comp (e1.symm.toLinearMap.comp e2.symm.toLinearMap)
    let g := (Representation.IntertwiningMap.equivLinearMapAsModule τ ν).symm G
    refine ⟨g.toLinearMap, ?_, fun h x => Representation.IntertwiningMap.isIntertwining _ _ g h x⟩
    intro h0
    have : IsSimpleModule (MonoidAlgebra ℂ H) τ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule τ).1 hτ
    haveI := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) τ.asModule
    obtain ⟨t, ht⟩ := exists_ne (0 : τ.asModule)
    have hG : G t = 0 := LinearMap.congr_fun h0 t
    have : (e1.symm (e2.symm t) : S) = 0 := Subtype.ext hG
    exact ht (by simpa using this)
