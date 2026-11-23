import Mathlib

namespace GlobalTheory

open Submodule

theorem exists_isCompl_isFullyInvariant_sum_images (R : Type) [Ring R] (M : Type) [AddCommGroup M]
    [Module R M] [IsSemisimpleModule R M] (x₀ : M) :
    ∃ C : Submodule R M, IsCompl (⨆ f : (R ∙ x₀) →ₗ[R] M, LinearMap.range f) C ∧
      C.IsFullyInvariant := by
  set Mξ : Submodule R M := ⨆ f : (R ∙ x₀) →ₗ[R] M, LinearMap.range f with hMξ
  have hinv : Mξ.IsFullyInvariant := by
    intro g
    refine iSup_le fun f => ?_
    rw [← Submodule.map_le_iff_le_comap, ← LinearMap.range_comp]
    exact le_iSup (fun f : (R ∙ x₀) →ₗ[R] M => LinearMap.range f) (g ∘ₗ f)
  let e := (OrderIso.setIsotypicComponents (R := R) (M := M))
  let m : fullyInvariantSubmodule R M := ⟨Mξ, hinv⟩
  let c : fullyInvariantSubmodule R M := e (e.symm m)ᶜ
  have h1 : IsCompl (e (e.symm m)) c := (e.isCompl_iff).mp isCompl_compl
  rw [e.apply_symm_apply] at h1
  refine ⟨c.1, ?_, c.2⟩
  constructor
  · rw [disjoint_iff]
    exact congrArg Subtype.val h1.inf_eq_bot
  · rw [codisjoint_iff]
    exact congrArg Subtype.val h1.sup_eq_top

theorem exists_isotypic_projector (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M] :
    IsSemisimpleModule R M → ∀ x₀ : M, ∃ P : M →ₗ[R] M, P x₀ = x₀ ∧ (∀ v, P (P v) = P v) ∧
      (∀ g : M →ₗ[R] M, ∀ v, P (g v) = g (P v)) ∧
      ∀ (W : Submodule R M), x₀ ∈ W → ∀ a : R, (∀ u ∈ W, a • u = 0) → ∀ v, a • P v = 0 := by
  intro hM x₀
  obtain ⟨C, hC, hCinv⟩ := exists_isCompl_isFullyInvariant_sum_images R M x₀
  set Mξ : Submodule R M := ⨆ f : (R ∙ x₀) →ₗ[R] M, LinearMap.range f with hMξ
  have hinv : Mξ.IsFullyInvariant := by
    intro g
    refine iSup_le fun f => ?_
    rw [← Submodule.map_le_iff_le_comap, ← LinearMap.range_comp]
    exact le_iSup (fun f : (R ∙ x₀) →ₗ[R] M => LinearMap.range f) (g ∘ₗ f)
  have hx : x₀ ∈ Mξ := by
    refine (le_iSup (fun f : (R ∙ x₀) →ₗ[R] M => LinearMap.range f) (R ∙ x₀).subtype) ?_
    exact ⟨⟨x₀, Submodule.mem_span_singleton_self x₀⟩, rfl⟩
  let P : M →ₗ[R] M := Mξ.subtype ∘ₗ Submodule.linearProjOfIsCompl Mξ C hC
  have hP : ∀ y ∈ Mξ, ∀ z ∈ C, P (y + z) = y := by
    intro y hy z hz
    simp only [P, LinearMap.comp_apply, map_add]
    have h1 : Submodule.linearProjOfIsCompl Mξ C hC y = ⟨y, hy⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨y, hy⟩
    have h2 : Submodule.linearProjOfIsCompl Mξ C hC z = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hC ⟨z, hz⟩
    rw [h1, h2]; simp
  have hdec : ∀ v : M, ∃ y ∈ Mξ, ∃ z ∈ C, y + z = v := by
    intro v
    have : v ∈ Mξ ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp this
  have hPmem : ∀ v, P v ∈ Mξ := fun v => (Submodule.linearProjOfIsCompl Mξ C hC v).2
  have hPy : ∀ y ∈ Mξ, P y = y := fun y hy => by simpa using hP y hy 0 C.zero_mem
  refine ⟨P, hPy x₀ hx, fun v => hPy _ (hPmem v), ?_, ?_⟩
  · intro g v
    obtain ⟨y, hy, z, hz, rfl⟩ := hdec v
    rw [hP y hy z hz, map_add, hP (g y) (hinv g hy) (g z) (hCinv g hz)]
  · intro W hW a ha v
    have hX : ∀ u : (R ∙ x₀), a • u = 0 := by
      intro u
      apply Subtype.ext
      exact ha u ((Submodule.span_singleton_le_iff_mem x₀ W).mpr hW u.2)
    have key : ∀ m ∈ Mξ, a • m = 0 := by
      intro m hm
      refine Submodule.iSup_induction _ (motive := fun m => a • m = 0) hm ?_ (smul_zero a) ?_
      · rintro f _ ⟨u, rfl⟩
        rw [← map_smul, hX u, map_zero]
      · intro m₁ m₂ h₁ h₂; rw [smul_add, h₁, h₂, add_zero]
    exact key _ (hPmem v)

end GlobalTheory
