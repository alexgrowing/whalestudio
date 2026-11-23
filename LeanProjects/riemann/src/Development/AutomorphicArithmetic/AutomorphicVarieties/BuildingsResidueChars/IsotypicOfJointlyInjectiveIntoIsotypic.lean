import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
open GlobalTheory.CuspRep

private theorem iSup_range_of_jointly_injective {R M S N I : Type} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S] [AddCommGroup N] [Module R N] [IsSimpleModule R S] [Finite I]
    (h : ∀ x : M, x ∈ ⨆ f : S →ₗ[R] M, LinearMap.range f) (j : I → N →ₗ[R] M)
    (hj : ∀ y, (∀ i, j i y = 0) → y = 0) (y : N) : y ∈ ⨆ f : S →ₗ[R] N, LinearMap.range f := by
  have hM : IsSemisimpleModule R M := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.1 fun x _ => ?_)
    refine (iSup_le (a := sSup {m : Submodule R M | IsSimpleModule R m}) fun f => ?_) (h x)
    rcases LinearMap.injective_or_eq_zero f with hf | rfl
    · exact le_sSup (IsSimpleModule.congr (LinearEquiv.ofInjective f hf).symm)
    · simp
  have hinj : Function.Injective (LinearMap.pi j) := by
    rw [injective_iff_map_eq_zero]
    exact fun z hz => hj z fun i => congrFun hz i
  have hN : IsSemisimpleModule R N := IsSemisimpleModule.congr (LinearEquiv.ofInjective _ hinj)
  have hy : y ∈ sSup {m : Submodule R N | IsSimpleModule R m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]; trivial
  refine (sSup_le (a := ⨆ f : S →ₗ[R] N, LinearMap.range f) fun m hm => ?_) hy
  have hm' : IsSimpleModule R m := hm
  by_cases hz : ∀ i, (j i).comp m.subtype = 0
  · intro z hzm
    have : z = 0 := hj z fun i => LinearMap.congr_fun (hz i) ⟨z, hzm⟩
    rw [this]; exact zero_mem _
  · obtain ⟨i, hi⟩ := not_forall.1 hz
    have hi' := (LinearMap.injective_or_eq_zero ((j i).comp m.subtype)).resolve_right hi
    obtain ⟨e⟩ := LocUniq.equiv_of_iSup_range h _ hi'
    intro z hzm
    exact Submodule.mem_iSup_of_mem (m.subtype.comp e.toLinearMap) ⟨e.symm ⟨z, hzm⟩, by simp⟩

theorem UpperTheory.isotypic_of_jointly_injective_into_isotypic :
    ∀ (Γ X V : Type) [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V), σ.IsIrreducible → (⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1) = ⊤ → ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ Γ Y) (I : Type) [Finite I] (j : I → Y →ₗ[ℂ] V), (∀ i g y, j i (ρ g y) = τ g (j i y)) → (∀ y, (∀ i, j i y = 0) → y = 0) → (⨆ f : {f : X →ₗ[ℂ] Y // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) = ⊤ := by
  intro Γ X V _ _ _ _ _ σ τ hσ h Y _ _ ρ I _ j hj hj0
  have key := iSup_range_of_jointly_injective (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule)
    (N := ρ.asModule) (fun x => by
      have hx : τ.asModuleEquiv x ∈ (⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)},
        LinearMap.range f.1) := h ▸ Submodule.mem_top
      have hle : (⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)},
          LinearMap.range f.1) ≤ ((⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule,
          LinearMap.range f).restrictScalars ℂ).comap τ.asModuleEquiv.symm.toLinearMap := by
        refine iSup_le fun f => ?_
        rintro _ ⟨v, rfl⟩
        let f' : σ.IntertwiningMap τ := ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
        have : Representation.IntertwiningMap.equivLinearMapAsModule σ τ f' (σ.asModuleEquiv.symm v) ∈
            ⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule, LinearMap.range f :=
          Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ f') ⟨_, rfl⟩
        exact this
      exact hle hx)
    (fun i => Representation.IntertwiningMap.equivLinearMapAsModule ρ τ ⟨j i, fun g => LinearMap.ext (hj i g)⟩)
    (fun y hy => hj0 y hy)
  refine top_le_iff.1 fun y _ => ?_
  refine Submodule.iSup_induction _ (motive := fun z : ρ.asModule => ρ.asModuleEquiv z ∈
    (⨆ f : {f : X →ₗ[ℂ] Y // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1))
    (key (ρ.asModuleEquiv.symm y)) ?_ ?_ ?_
  · rintro f _ ⟨v, rfl⟩
    let f' := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ).symm f
    exact Submodule.mem_iSup_of_mem ⟨f'.toLinearMap, fun g v => LinearMap.congr_fun (f'.isIntertwining' g) v⟩
      ⟨σ.asModuleEquiv v, rfl⟩
  · rw [map_zero]; exact zero_mem _
  · intro a b ha hb
    rw [map_add]; exact add_mem ha hb
