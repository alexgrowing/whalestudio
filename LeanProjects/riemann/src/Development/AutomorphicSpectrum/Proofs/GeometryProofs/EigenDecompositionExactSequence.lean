import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes

open NumberField GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigExact

theorem mem_eigSp_iff {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]
    {ρ : O →+* Module.End k V} {τ : O →+* k} {x : V} : x ∈ eigSp ρ τ ↔ ∀ a, ρ a x = τ a • x := by
  simp [eigSp, sub_eq_zero]

theorem eigSp_eq_eigenSub {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]
    (ρ : O →+* Module.End k V) (τ : O →+* k) : eigSp ρ τ = EigenSplit.eigenSub ρ τ := by
  ext x
  rw [mem_eigSp_iff, EigenSplit.mem_eigenSub]

theorem map_eigSp_eq {E : Type} [Field E] [NumberField E] {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {V₂ V₃ : Type} [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    {ρ₂ : 𝓞 E →+* Module.End k V₂} {ρ₃ : 𝓞 E →+* Module.End k V₃} {g : V₂ →ₗ[k] V₃}
    (hg : Function.Surjective g) (hgρ : ∀ a x, g (ρ₂ a x) = ρ₃ a (g x)) (τ : 𝓞 E →+* k) :
    (eigSp ρ₂ τ).map g = eigSp ρ₃ τ := by
  classical
  obtain ⟨φ, rfl⟩ := GlobalTheory.TraceSpread.exists_embedding τ
  have hs := GlobalTheory.TraceSpread.isSplitting_embeddings (E := E) k
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hx
    rw [mem_eigSp_iff]
    intro a
    rw [← hgρ, hx, map_smul]
  · intro y hy
    obtain ⟨x, rfl⟩ := hg y
    rw [eigSp_eq_eigenSub] at hy
    refine ⟨EigenSplit.proj hs ρ₂ φ x, ?_, ?_⟩
    · rw [SetLike.mem_coe, eigSp_eq_eigenSub]
      exact EigenSplit.proj_mem hs ρ₂ φ x
    · have he : EigenSplit.IsEquivariant ρ₂ ρ₃ g := hgρ
      rw [he.proj hs φ x]
      exact EigenSplit.proj_of_mem hs hy

theorem eigSp_inf_ker {O k V₁ V₂ V₃ : Type} [CommRing O] [Field k] [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    {ρ₁ : O →+* Module.End k V₁} {ρ₂ : O →+* Module.End k V₂} {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃}
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hfρ : ∀ a x, f (ρ₁ a x) = ρ₂ a (f x)) (τ : O →+* k) :
    eigSp ρ₂ τ ⊓ LinearMap.ker g = (eigSp ρ₁ τ).map f := by
  apply le_antisymm
  · rintro x ⟨hx, hk⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hx
    have hk' : x ∈ LinearMap.range f := by rw [hfg]; exact hk
    obtain ⟨z, rfl⟩ := hk'
    refine ⟨z, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff]
    intro a
    apply hf
    rw [hfρ, hx, map_smul]
  · rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp_iff] at hz
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, mem_eigSp_iff]
      intro a
      rw [← hfρ, hz, map_smul]
    · change f z ∈ LinearMap.ker g
      rw [← hfg]
      exact ⟨z, rfl⟩

theorem finrank_map_add_inf_ker {k V W : Type} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (g : V →ₗ[k] W) (S : Submodule k V) [FiniteDimensional k S] :
    Module.finrank k (S.map g) + Module.finrank k ↥(S ⊓ LinearMap.ker g) = Module.finrank k S := by
  have h := LinearMap.finrank_range_add_finrank_ker (g.domRestrict S)
  rw [LinearMap.range_domRestrict] at h
  rw [← h, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker g)),
    Submodule.map_comap_subtype]

theorem exists_basis_eigSp_quot : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃] (ρ₁ : 𝓞 E →+* Module.End k V₁) (ρ₂ : 𝓞 E →+* Module.End k V₂) (ρ₃ : 𝓞 E →+* Module.End k V₃) (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃), Function.Injective f → Function.Surjective g → LinearMap.range f = LinearMap.ker g → (∀ a x, f (ρ₁ a x) = ρ₂ a (f x)) → (∀ a x, g (ρ₂ a x) = ρ₃ a (g x)) → ∀ (τ : 𝓞 E →+* k) (r n : ℕ) (b₁ : Fin r → V₁) (b₂ : Fin n → V₂), LinearIndependent k b₁ → Submodule.span k (Set.range b₁) = eigSp ρ₁ τ → LinearIndependent k b₂ → Submodule.span k (Set.range b₂) = eigSp ρ₂ τ → r ≤ n ∧ ∃ b₃ : Fin (n - r) → V₃, LinearIndependent k b₃ ∧ Submodule.span k (Set.range b₃) = eigSp ρ₃ τ := by
  intro E _ _ k _ _ _ V₁ V₂ V₃ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hfg hfρ hgρ τ r n b₁ b₂ hb₁ hs₁ hb₂ hs₂
  have hr : Module.finrank k (eigSp ρ₁ τ) = r := by
    rw [← hs₁, finrank_span_eq_card hb₁, Fintype.card_fin]
  have hn : Module.finrank k (eigSp ρ₂ τ) = n := by
    rw [← hs₂, finrank_span_eq_card hb₂, Fintype.card_fin]
  haveI : FiniteDimensional k (eigSp ρ₂ τ) := by
    rw [← hs₂]
    exact FiniteDimensional.span_of_finite k (Set.finite_range b₂)
  have hsum := finrank_map_add_inf_ker g (eigSp ρ₂ τ)
  rw [map_eigSp_eq hg hgρ τ, eigSp_inf_ker hf hfg hfρ τ, ← (Submodule.equivMapOfInjective f hf (eigSp ρ₁ τ)).finrank_eq, hr, hn] at hsum
  haveI : FiniteDimensional k (eigSp ρ₃ τ) := by
    rw [← map_eigSp_eq hg hgρ τ]
    infer_instance
  have h3 : Module.finrank k (eigSp ρ₃ τ) = n - r := by omega
  refine ⟨by omega, ?_⟩
  let B := Module.finBasisOfFinrankEq k (eigSp ρ₃ τ) h3
  refine ⟨fun i => (B i : V₃), ?_, ?_⟩
  · exact B.linearIndependent.map' (eigSp ρ₃ τ).subtype (Submodule.ker_subtype _)
  · have : Set.range (fun i => (B i : V₃)) = (eigSp ρ₃ τ).subtype '' Set.range B := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.CompanionTheory.Ar.EigExact
