import Mathlib

namespace GlobalTheory

open Classical in

theorem iSup_stable_inf_typeSpace {G E C : Type} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* ℂˣ) (U : C → Submodule ℂ E) (S : C → Prop)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) :
    (⨆ (c : C) (_ : S c), U c) ⊓
        (⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) =
      ⨆ (c : C) (_ : S c), U c ⊓
        (⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) := by
  set K : Submodule ℂ E :=
    ⨅ h : P, LinearMap.ker (ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id) with hK
  have memK : ∀ x, x ∈ K ↔ ∀ h : P, ρ (h : G) x = ((ψ h : ℂˣ) : ℂ) • x := by
    intro x
    simp [hK, Submodule.mem_iInf, sub_eq_zero]
  have hc : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let T : E →ₗ[ℂ] E :=
    (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G)
  have hT : ∀ x, T x = (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G) x := by
    intro x
    simp only [T, LinearMap.smul_apply, LinearMap.sum_apply]
  have h1 : ∀ x ∈ K, T x = x := by
    intro x hx
    rw [hT]
    have : ∀ h : P, (((ψ h)⁻¹ : ℂˣ) : ℂ) • ρ (h : G) x = x := by
      intro h
      rw [(memK x).1 hx h, smul_smul, Units.inv_mul, one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : ∀ x, T x ∈ K := by
    intro x
    rw [memK]
    intro k
    rw [hT, map_smul, smul_comm]
    congr 1
    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
    intro h
    simp only [Equiv.coe_mulLeft, map_smul, map_mul, Subgroup.coe_mul, Module.End.mul_apply,
      smul_smul]
    congr 1
    rw [← Units.val_mul, mul_inv_rev, mul_comm (ψ h)⁻¹, mul_inv_cancel_left]
  have h3 : ∀ c, ∀ x ∈ U c, T x ∈ U c := by
    intro c x hx
    rw [hT]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun h _ =>
      Submodule.smul_mem _ _ (hU c h (Submodule.mem_map_of_mem hx)))
  apply le_antisymm
  · rintro x ⟨hx, hxK⟩
    have hle : (⨆ (c : C) (_ : S c), U c) ≤ (⨆ (c : C) (_ : S c), U c ⊓ K).comap T := by
      refine iSup₂_le fun c hc y hy => ?_
      exact (le_iSup₂_of_le (f := fun (c : C) (_ : S c) => U c ⊓ K) c hc le_rfl)
        (show T y ∈ U c ⊓ K from ⟨h3 c y hy, h2 y⟩)
    have := hle hx
    rwa [Submodule.mem_comap, h1 x hxK] at this
  · exact iSup₂_le fun c hc => inf_le_inf_right _
      (le_iSup₂_of_le (f := fun (c : C) (_ : S c) => U c) c hc le_rfl)

end GlobalTheory
