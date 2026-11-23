import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
open GlobalTheory.MeetsGen

noncomputable section
namespace GlobalTheory.MeetsTypeVec

theorem lift_apply_mem {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (W : Submodule K V) (hW : ∀ g x, x ∈ W → φ g x ∈ W)
    (a : MonoidAlgebra K G) {x : V} (hx : x ∈ W) :
    MonoidAlgebra.lift K (Module.End K V) G φ a x ∈ W := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => by
    rw [LinearMap.smul_apply]; exact W.smul_mem _ (hW g x hx)

theorem proj_eigen {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (y : V) (u' : U) :
    φ u' (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y)
      = ((ψ u' : Kˣ) : K) • MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y := by
  have hφ : ∀ u : U, φ u' (φ u y) = φ ((u' * u : U) : G) y := by
    intro u; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp only [pU, map_sum, MonoidAlgebra.lift_single, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    Finset.smul_sum, hφ]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, smul_smul]
  congr 1
  simp only [map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : ((ψ u' : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

theorem meets : ∀ {K G V : Type} [Field K] [Group G] [Fintype G] [AddCommGroup V] [Module K V] (ρ : G →* (V ≃ₗ[K] V)) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (e : MonoidAlgebra K G) (b : G → MonoidAlgebra K G), e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)) * b g → ∀ (W : Submodule K V), W ≠ ⊥ → (∀ g x, x ∈ W → ρ g x ∈ W) → (∀ x ∈ W, MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) e x = x) → W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) ≠ ⊥ := by
  intro K G V _ _ _ _ _ ρ U _ ψ e b he W hW0 hWs hWe
  set φ : G →* Module.End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ with hφdef
  have hφ : ∀ g x, φ g x = ρ g x := fun _ _ => rfl
  have hWs' : ∀ g x, x ∈ W → φ g x ∈ W := fun g x hx => by rw [hφ]; exact hWs g x hx
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hsum : x = ∑ g : G, φ g (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x)) := by
    conv_lhs => rw [← hWe x hxW, he]
    simp only [map_sum, map_mul, MonoidAlgebra.lift_single, one_smul, LinearMap.sum_apply, Module.End.mul_apply]
  intro hbot
  apply hx0
  rw [hsum]
  refine Finset.sum_eq_zero fun g _ => ?_
  have hmem : MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x) ∈
      W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) := by
    refine ⟨lift_apply_mem φ W hWs' _ (lift_apply_mem φ W hWs' _ hxW), ?_⟩
    refine Submodule.mem_iInf _ |>.2 fun u => LinearMap.mem_ker.2 ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ← hφ, proj_eigen,
      sub_self]
  rw [hbot] at hmem
  rw [(Submodule.mem_bot K).1 hmem, map_zero]

end GlobalTheory.MeetsTypeVec
