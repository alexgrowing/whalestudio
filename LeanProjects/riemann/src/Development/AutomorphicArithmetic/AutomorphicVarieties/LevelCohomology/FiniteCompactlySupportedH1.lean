import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KrullDimQuotientComapEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem ker_open {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M) (h : ContAction ρ) :
    IsOpen (ρ.ker : Set Γ) := by
  let b := Module.finBasis k M
  have hset : (ρ.ker : Set Γ) = ⋂ i, {g | ρ g (b i) = b i} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg i
      rw [hg]
      rfl
    · intro hg
      exact b.ext fun i => by simpa using hg i
  rw [hset]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous fun g : Γ => ρ g (b i) :=
    (show Continuous fun p : Γ × M => ρ p.1 p.2 from h).comp (continuous_id.prodMk continuous_const)
  exact hc.isOpen_preimage {b i} (isOpen_discrete _)

private theorem finite_compactly_supported_H1 {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)
    [Module.Finite k (H1 ρ)] : Module.Finite k (F.H1c ρ) := by
  have hB : (B1 ρ).FG := by
    show (LinearMap.range (d0 ρ)).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  haveI : IsNoetherian k ↥(B1 ρ) := isNoetherian_of_fg_of_noetherian _ hB
  have hK : (Submodule.comap (Z1 ρ).subtype (B1 ρ)).FG :=
    Submodule.fg_of_fg_map_injective (Z1 ρ).subtype Subtype.val_injective
      (Submodule.FG.of_le_of_isNoetherian (Submodule.map_comap_le _ _))
  have hZ : (⊤ : Submodule k ↥(Z1 ρ)).FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Submodule.comap (Z1 ρ).subtype (B1 ρ)))
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq, Submodule.ker_mkQ]
      exact hK
  haveI : Module.Finite k ↥(Z1 ρ) := ⟨hZ⟩
  have hZ1 : (Z1 ρ).FG := Module.Finite.iff_fg.mp inferInstance
  have hP : ((Z1 ρ).prod (⊤ : Submodule k (F.T → M))).FG := hZ1.prod Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : F.H1c ρ ≤ (Z1 ρ).prod ⊤ := by
    rintro x ⟨hlc, hcoc, -, -, -⟩
    exact ⟨⟨hlc.continuous, hcoc⟩, trivial⟩
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)

theorem UpperTheory.V.X.framed_h1_euler_formula :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M), ContAction ρ → (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (H1 ρ) → Module.Finite k (F.H1c ρ) ∧ finrank k (F.H1c ρ) + finrank k (H0 ρ) = finrank k (selF F ρ) + ∑ v, finrank k (H0 (ρ.comp (F.φ v))) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ F ρ hc hN hH
  refine ⟨finite_compactly_supported_H1 F ρ, ?_⟩
  have e := Alg.finrank_compact_support_H1 k Γ M ρ (ker_open ρ hc) F hN hH
  have hs : finrank k ↥(selF F ρ) = finrank k ↥(Sha1 ρ F.φ F.hφ ⊓
      Sel ρ F.ψ F.hψ fun q => H1ur (ρ.comp (F.ψ q)) (F.N q)) := rfl
  rw [hs]
  omega
