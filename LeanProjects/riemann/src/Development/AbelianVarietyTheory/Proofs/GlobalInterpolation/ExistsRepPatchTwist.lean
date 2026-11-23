import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N

namespace GlobalTheory

theorem exists_hom_patch_of_agree {Γ G : Type*} [Group Γ] [Group G] (a b : Γ →* G)
    (η₀ η : Γ →* ℤˣ) (s : Γ) (h0 : η₀ s = 1) (h1 : η s = -1)
    (hab : ∀ g, η₀ g = 1 → η g = 1 → b g = a g)
    (hc : ∀ y : G, (∀ g, η₀ g = 1 → η g = 1 → a g * y = y * a g) → a s * y = y * a s) :
    ∃ ρ : Γ →* G, (∀ g, η₀ g = 1 → ρ g = a g) ∧ ∀ g, η g = 1 → ρ g = b g := by
  classical
  by_cases ht : ∃ t, η₀ t = -1 ∧ η t = 1
  swap
  · refine ⟨a, fun g _ => rfl, fun g hg => ?_⟩
    rcases Int.units_eq_one_or (η₀ g) with h | h
    · exact (hab g h hg).symm
    · exact absurd ⟨g, h, hg⟩ ht
  obtain ⟨t, ht0, ht1⟩ := ht
  set z := (a t)⁻¹ * b t with hz
  have hzK : ∀ g, η₀ g = 1 → η g = 1 → a g * z = z * a g := by
    intro g hg0 hg1
    have e : b (t * g * t⁻¹) = a (t * g * t⁻¹) :=
      hab _ (by simp only [map_mul, map_inv, hg0, mul_one, mul_inv_cancel])
        (by simp only [map_mul, map_inv, hg1, mul_one, mul_inv_cancel])
    simp only [map_mul, map_inv, hab g hg0 hg1] at e
    rw [hz]
    calc a g * ((a t)⁻¹ * b t) = (a t)⁻¹ * (a t * a g * (a t)⁻¹) * b t := by group
      _ = (a t)⁻¹ * (b t * a g * (b t)⁻¹) * b t := by rw [e]
      _ = (a t)⁻¹ * b t * a g := by group
  have hzs : a s * z = z * a s := hc z hzK
  have hzH0 : ∀ g, η₀ g = 1 → a g * z = z * a g := by
    intro g hg0
    rcases Int.units_eq_one_or (η g) with hg1 | hg1
    · exact hzK g hg0 hg1
    · have hk0 : η₀ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, h0, hg0]; decide
      have hk1 : η (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, h1, hg1]; decide
      have hk := hzK _ hk0 hk1
      have hg : a g = a s * a (s⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
      rw [hg, mul_assoc, hk, ← mul_assoc, hzs, mul_assoc]
  have hzz : ∀ g, η₀ g = -1 → z * a g * z = a g := by
    intro g hg0
    have hm : η₀ (t⁻¹ * g) = 1 := by rw [map_mul, map_inv, ht0, hg0]; decide
    have hg : a g = a t * a (t⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
    have ht2 : b (t * t) = a (t * t) :=
      hab _ (by rw [map_mul, ht0]; decide) (by rw [map_mul, ht1]; decide)
    rw [map_mul, map_mul] at ht2
    rw [hg]
    calc z * (a t * a (t⁻¹ * g)) * z = z * a t * (a (t⁻¹ * g) * z) := by group
      _ = z * a t * (z * a (t⁻¹ * g)) := by rw [hzH0 _ hm]
      _ = (a t)⁻¹ * (b t * b t) * a (t⁻¹ * g) := by rw [hz]; group
      _ = a t * a (t⁻¹ * g) := by rw [ht2]; group
  have hn : ∀ u : ℤˣ, u = -1 → ¬ u = 1 := by rintro u rfl; decide
  refine ⟨MonoidHom.mk' (fun g => if η₀ g = 1 then a g else a g * z) ?_, ?_, ?_⟩
  · intro g g'
    rcases Int.units_eq_one_or (η₀ g) with h | h <;> rcases Int.units_eq_one_or (η₀ g') with h' | h'
    · rw [if_pos (by rw [map_mul, h, h']; decide), if_pos h, if_pos h', map_mul]
    · rw [if_neg (hn _ (by rw [map_mul, h, h']; decide)), if_pos h, if_neg (hn _ h'), map_mul, mul_assoc]
    · rw [if_neg (hn _ (by rw [map_mul, h, h']; decide)), if_neg (hn _ h), if_pos h', map_mul,
        mul_assoc, mul_assoc, hzH0 g' h']
    · rw [if_pos (by rw [map_mul, h, h']; decide), if_neg (hn _ h), if_neg (hn _ h'), map_mul,
        mul_assoc, ← mul_assoc z, hzz g' h']
  · intro g hg
    rw [MonoidHom.mk'_apply, if_pos hg]
  · intro g hg
    rw [MonoidHom.mk'_apply]
    rcases Int.units_eq_one_or (η₀ g) with h | h
    · rw [if_pos h, hab g h hg]
    · rw [if_neg (hn _ h)]
      have hk : b (g * t⁻¹) = a (g * t⁻¹) :=
        hab _ (by rw [map_mul, map_inv, h, ht0]; decide) (by rw [map_mul, map_inv, hg, ht1]; decide)
      simp only [map_mul, map_inv] at hk
      rw [hz]
      calc a g * ((a t)⁻¹ * b t) = a g * (a t)⁻¹ * b t := by group
        _ = b g * (b t)⁻¹ * b t := by rw [hk]
        _ = b g := by group

theorem exists_rep_patch_twist : ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (ρ₀ ρ' : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ) (P : GL (Fin n) k) (s : Γ), η₀ s = 1 → η s = -1 → (∀ g, η₀ g = 1 → η g = 1 → ρ' g = P⁻¹ * ρ₀ g * P) → (∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∃ ρ : Γ →* GL (Fin n) k, (∀ g, η₀ g = 1 → ρ g = ρ₀ g) ∧ ∀ g, η g = 1 → ρ g = P * ρ' g * P⁻¹ := by
  intro Γ k _ _ n ρ₀ ρ' η₀ η P s hs0 hs1 hagree hcomm
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_hom_patch_of_agree ρ₀ ((MulAut.conj P).toMonoidHom.comp ρ') η₀ η s hs0 hs1
    (fun g h0 h1 => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hagree g h0 h1]
      group)
    (fun y hy => by
      apply Units.ext
      simp only [Units.val_mul]
      apply hcomm
      intro g h0 h1
      simpa only [Units.val_mul] using congrArg Units.val (hy g h0 h1))
  refine ⟨ρ, hρ0, fun g hg => ?_⟩
  rw [hρ1 g hg]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end GlobalTheory
