import Mathlib

noncomputable def UpperTheory.Reformulated.B.SubgroupFixed.HasFixed :
    {Γ V : Type} →
      [inst : Group Γ] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ Γ V → Subgroup Γ → Prop :=
    fun {Γ V : Type} [Group Γ] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ Γ V) (U : Subgroup Γ) ↦
      ∃ (v : V), v ≠ (0 : V) ∧ ∀ u ∈ U, ((ρ : Γ → V →ₗ[ℂ] V) u : V → V) v = v

private lemma UpperTheory.Reformulated.B.SubgroupFixed.core {R M N : Type*} [Ring R] [AddCommGroup M] [_root_.Module R M]
    [AddCommGroup N] [_root_.Module R N] [IsSimpleModule R M]
    (hsup : ∀ S : Submodule R N, (∀ f : M →ₗ[R] N, LinearMap.range f ≤ S) → S = ⊤)
    (W : Submodule R N) (hW : W ≠ ⊥) :
    ∃ g : M →ₗ[R] N, Function.Injective g ∧ LinearMap.range g ≤ W := by
  have hss : IsSemisimpleModule R N := by
    refine isSemisimpleModule_of_isSemisimpleModule_submodule'
      (p := fun f : M →ₗ[R] N => LinearMap.range f) (fun f => IsSemisimpleModule.range f) ?_
    exact hsup _ (fun f => le_iSup (fun f : M →ₗ[R] N => LinearMap.range f) f)
  obtain ⟨C, hC⟩ := exists_isCompl W
  let p : N →ₗ[R] W := W.linearProjOfIsCompl C hC
  have hex : ∃ f : M →ₗ[R] N, p ∘ₗ f ≠ 0 := by
    by_contra hno
    push Not at hno
    have htop : LinearMap.ker p = ⊤ := hsup _ (fun f => by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (hno f) x)
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have h1 : p w = 0 := by
      have : w ∈ LinearMap.ker p := htop ▸ Submodule.mem_top
      exact this
    have h2 : p w = ⟨w, hw⟩ := Submodule.linearProjOfIsCompl_apply_left hC ⟨w, hw⟩
    have h3 : (⟨w, hw⟩ : W) = 0 := h2.symm.trans h1
    simpa using congrArg Subtype.val h3
  obtain ⟨f, hf⟩ := hex
  have hinj := (LinearMap.injective_or_eq_zero (p ∘ₗ f)).resolve_right hf
  refine ⟨W.subtype ∘ₗ p ∘ₗ f, W.injective_subtype.comp hinj, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (p (f x)).2

theorem UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed :
    ∀ {Γ X V : Type} [inst : Group Γ] [inst_1 : AddCommGroup X] [inst_2 : _root_.Module ℂ X] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (σ : Representation ℂ Γ X),
      σ.IsIrreducible →
        ∀ (τ : Representation ℂ Γ V),
          ⨆ (f :
                { f : X →ₗ[ℂ] V //
                  ∀ (g : Γ) (v : X),
                    (f : X → V) (((σ : Γ → X →ₗ[ℂ] X) g : X → X) v) = ((τ : Γ → V →ₗ[ℂ] V) g : V → V) ((f : X → V) v) }),
                (↑f : X →ₗ[ℂ] V).range =
              ⊤ →
            ∀ (W : Submodule ℂ V),
              (∀ (g : Γ), ∀ v ∈ W, ((τ : Γ → V →ₗ[ℂ] V) g : V → V) v ∈ W) →
                W ≠ ⊥ →
                  ∀ (K : Subgroup Γ),
                    UpperTheory.Reformulated.B.SubgroupFixed.HasFixed σ K → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ u ∈ K, ((τ : Γ → V →ₗ[ℂ] V) u : V → V) v = v := by
  intro Γ X V _ _ _ _ _ σ hσ τ h W hWinv hW K hK
  obtain ⟨x0, hx0, hfix⟩ := hK
  haveI : IsSimpleModule (MonoidAlgebra ℂ Γ) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  let W' : Submodule (MonoidAlgebra ℂ Γ) τ.asModule :=
    { carrier := {x | τ.asModuleEquiv x ∈ W}
      add_mem' := fun {a b} ha hb => by
        show τ.asModuleEquiv (a + b) ∈ W
        rw [map_add]
        exact W.add_mem ha hb
      zero_mem' := by
        show τ.asModuleEquiv 0 ∈ W
        rw [map_zero]
        exact W.zero_mem
      smul_mem' := fun r x hx => by
        show τ.asModuleEquiv (r • x) ∈ W
        rw [Representation.asModuleEquiv_map_smul]
        exact τ.asAlgebraHom_mem_of_forall_mem W hWinv _ hx r }
  have hW' : W' ≠ ⊥ := by
    intro hbot
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have hmem : τ.asModuleEquiv.symm w ∈ W' := by
      show τ.asModuleEquiv (τ.asModuleEquiv.symm w) ∈ W
      simpa using hw
    rw [hbot, Submodule.mem_bot] at hmem
    simpa using hmem
  have hsup : ∀ S : Submodule (MonoidAlgebra ℂ Γ) τ.asModule,
      (∀ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule, LinearMap.range f ≤ S) → S = ⊤ := by
    intro S hS
    let S0 : Submodule ℂ V :=
      (S.restrictScalars ℂ).comap (τ.asModuleEquiv.symm : V →ₗ[ℂ] τ.asModule)
    have hS0 : S0 = ⊤ := by
      rw [eq_top_iff, ← h]
      refine iSup_le fun f => ?_
      rintro _ ⟨x, rfl⟩
      let F : Representation.IntertwiningMap σ τ :=
        f.1.intertwiningMap_of_isIntertwiningMap σ τ f.2
      exact hS (Representation.IntertwiningMap.equivLinearMapAsModule σ τ F)
        ⟨σ.asModuleEquiv.symm x, rfl⟩
    rw [eq_top_iff]
    intro y _
    have hy : τ.asModuleEquiv y ∈ S0 := hS0 ▸ Submodule.mem_top
    simpa [S0] using hy
  obtain ⟨g, hg, hgW⟩ := UpperTheory.Reformulated.B.SubgroupFixed.core hsup W' hW'
  refine ⟨τ.asModuleEquiv (g (σ.asModuleEquiv.symm x0)), hgW ⟨_, rfl⟩, ?_, ?_⟩
  · intro h0
    have h1 : g (σ.asModuleEquiv.symm x0) = 0 := by simpa using h0
    have h2 : σ.asModuleEquiv.symm x0 = 0 := hg (h1.trans (map_zero g).symm)
    exact hx0 (by simpa using h2)
  · intro u hu
    apply τ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply, ← map_smul,
      ← Representation.asModuleEquiv_symm_map_rho, hfix u hu]
