import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsStableSubmoduleTopWeightLine
open Formalism.REAL

namespace GlobalTheory

theorem stable_submodule_proj_bijective {U V₁ V₂ : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ U) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
    (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v : U)
    (p : U →ₗ[ℂ] V₁) (q : U →ₗ[ℂ] V₂)
    (hp : ∀ a b x, p (E a b x) = E₁ a b (p x)) (hq : ∀ a b x, q (E a b x) = E₂ a b (q x))
    (hpq : ∀ x, p x = 0 → q x = 0 → x = 0)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (h₂ : ∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw : ∀ a, E₁ a a (p v) = ν a • p v) (hv₁ : p v ≠ 0) (hv₂ : q v ≠ 0)
    (S : Submodule ℂ U) (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (hvS : v ∈ S)
    (htop : ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v) :
    Function.Bijective (q.comp S.subtype) := by
  constructor
  · have hK := h₁ ((S ⊓ LinearMap.ker q).map p) (by
      rintro a b _ ⟨x, ⟨hxS, hxq⟩, rfl⟩
      refine ⟨E a b x, ⟨hS a b x hxS, ?_⟩, hp a b x⟩
      have hxq' : q x = 0 := hxq
      show q (E a b x) = 0
      rw [hq, hxq', map_zero])
    rcases hK with hK | hK
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : q x = 0 := hx
      have hm : p x ∈ (S ⊓ LinearMap.ker q).map p := ⟨x, ⟨x.2, hx'⟩, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact Subtype.ext (hpq _ hm hx')
    · exfalso
      have hm : p v ∈ (S ⊓ LinearMap.ker q).map p := by rw [hK]; trivial
      obtain ⟨x, ⟨hxS, hxq⟩, hxp⟩ := hm
      have hxq' : q x = 0 := hxq
      obtain ⟨c, hc⟩ := htop x hxS (fun a => by
        rw [← sub_eq_zero]
        apply hpq
        · rw [map_sub, hp, map_smul, hxp, hw, sub_self]
        · rw [map_sub, hq, map_smul, hxq', map_zero, smul_zero, sub_self])
      rw [hc, map_smul, smul_eq_zero] at hxq'
      rcases hxq' with h0 | h0
      · apply hv₁
        rw [← hxp, hc, h0, zero_smul, map_zero]
      · exact hv₂ h0
  · have hK := h₂ (S.map q) (by
      rintro a b _ ⟨x, hxS, rfl⟩
      exact ⟨E a b x, hS a b x hxS, hq a b x⟩)
    rcases hK with hK | hK
    · exfalso
      have hm : q v ∈ S.map q := ⟨v, hvS, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact hv₂ hm
    · intro y
      have hm : y ∈ S.map q := by rw [hK]; trivial
      obtain ⟨x, hxS, rfl⟩ := hm
      exact ⟨⟨x, hxS⟩, rfl⟩

theorem exists_linearEquiv_of_irreducible_isHW :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v₁ : V₁) (v₂ : V₂), GlRel E₁ → GlRel E₂ → (∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → IsHW E₁ ν v₁ → IsHW E₂ ν v₂ → v₁ ≠ 0 → v₂ ≠ 0 → ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ V₂ _ _ n E₁ E₂ ν v₁ v₂ hE₁ hE₂ h₁ h₂ hw₁ hw₂ hv₁ hv₂
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  have b₂ := stable_submodule_proj_bijective E E₁ E₂ ν (v₁, v₂) (LinearMap.fst ℂ V₁ V₂)
    (LinearMap.snd ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h h') h₁ h₂ hw₁.1 hv₁ hv₂ S hS hvS htop
  have b₁ := stable_submodule_proj_bijective E E₂ E₁ ν (v₁, v₂) (LinearMap.snd ℂ V₁ V₂)
    (LinearMap.fst ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h' h) h₂ h₁ hw₂.1 hv₂ hv₁ S hS hvS htop
  refine ⟨(LinearEquiv.ofBijective _ b₁).symm.trans (LinearEquiv.ofBijective _ b₂), ?_⟩
  intro a b x
  obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ b₁).surjective x
  have h : E₁ a b (LinearEquiv.ofBijective _ b₁ y)
      = LinearEquiv.ofBijective _ b₁ ⟨E a b y, hS a b y y.2⟩ := rfl
  rw [h]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory
