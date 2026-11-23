import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration

set_option autoImplicit false
noncomputable section
open Module

namespace GlobalTheory.AnnIso

theorem pairing_vanishes_of_annihilator_isotropic : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (N : Type 1) [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (g : ℕ),
    Module.Finite R N → Module.Projective R N → (∀ P : PrimeSpectrum R, Module.rankAtStalk N P = 2 * g) →
    ∀ b : M →ₗ[R] M →ₗ[R] R, b.IsPerfPair →
    ∀ φ : Module.Dual R N →ₗ[R] Module.Dual R N →ₗ[R] R,
      (∀ (x y : Module.Dual R N) (u v : M), (∀ w, x (e w) = b w u) → (∀ w, y (e w) = b w v) →
        φ x y = b u v) →
    ∀ S : Submodule R N, (∃ S' : Submodule R N, IsCompl S S') →
      (∀ P : PrimeSpectrum R, Module.rankAtStalk S P = g) →
      (∀ x y : Module.Dual R N, (∀ c ∈ S, x c = 0) → (∀ c ∈ S, y c = 0) → φ x y = 0) →
      ∀ u v : M, e u ∈ S → e v ∈ S → b u v = 0 := by
  intro R _ M _ _ N _ _ e g hfin hproj hrk b hb φ hφ S ⟨S', hc⟩ hS hiso u v hu hv
  let β : M ≃ₗ[R] Dual R M := LinearEquiv.ofBijective b.flip hb.bijective_right
  let γ : M ≃ₗ[R] Dual R N := β.trans e.symm.dualMap
  have hγ : ∀ (u w : M), γ u (e w) = b w u := by
    intro u w
    simp [γ, β]
  have hφγ : φ = b.compl₁₂ γ.symm.toLinearMap γ.symm.toLinearMap := by
    ext x y
    obtain ⟨u', rfl⟩ := γ.surjective x
    obtain ⟨v', rfl⟩ := γ.surjective y
    simp [hφ _ _ u' v' (hγ u') (hγ v')]
  haveI : φ.IsPerfPair := hφγ ▸ inferInstance
  have hpS : (S.projectionOnto S' hc) ∘ₗ S.subtype = LinearMap.id :=
    LinearMap.ext fun x ↦ Submodule.projectionOnto_apply_left hc x
  haveI : Module.Projective R S := Module.Projective.of_split _ _ hpS
  haveI : Module.Finite R S := Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective hc)
  have key := GlobalTheory.PolExistsRing.mem_of_annihilates_dual φ S S' hc g hrk hS
    (fun x hx y hy ↦ hiso x y ((Submodule.mem_dualAnnihilator _).1 hx)
      ((Submodule.mem_dualAnnihilator _).1 hy)) (γ v) (fun h hh ↦ by
        obtain ⟨v', rfl⟩ := γ.surjective h
        rw [hφ _ _ v v' (hγ v) (hγ v'), ← hγ v' v]
        exact (Submodule.mem_dualAnnihilator _).1 hh _ hv)
  rw [← hγ v u]
  exact (Submodule.mem_dualAnnihilator _).1 key _ hu

end GlobalTheory.AnnIso
