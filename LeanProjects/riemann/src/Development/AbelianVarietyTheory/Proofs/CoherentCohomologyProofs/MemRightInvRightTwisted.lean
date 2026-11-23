import Mathlib

namespace GlobalTheory.TwistedInverseSubgroups

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]

def leftInvLeftTwisted (H : Subgroup G) (γ : G) (T : E →ₗ[ℂ] E) : Submodule ℂ (G → E) where
  carrier := {f | (∀ h ∈ H, ∀ g, f (h * g) = f g) ∧ ∀ g, f (γ * g) = T (f g)}
  add_mem' := by
    rintro f₁ f₂ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    exact ⟨fun h hh g => by simp [a₁ h hh g, a₂ h hh g], fun g => by simp [b₁ g, b₂ g]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, b⟩
    exact ⟨fun h hh g => by simp [a h hh g], fun g => by simp [b g]⟩

def leftInvRightTwisted (H : Subgroup G) (γ : G) (T : E →ₗ[ℂ] E) : Submodule ℂ (G → E) where
  carrier := {f | (∀ h ∈ H, ∀ g, f (h * g) = f g) ∧ ∀ g, f (g * γ) = T (f g)}
  add_mem' := by
    rintro f₁ f₂ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    exact ⟨fun h hh g => by simp [a₁ h hh g, a₂ h hh g], fun g => by simp [b₁ g, b₂ g]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, b⟩
    exact ⟨fun h hh g => by simp [a h hh g], fun g => by simp [b g]⟩

def rightInvLeftTwisted (H : Subgroup G) (γ : G) (T : E →ₗ[ℂ] E) : Submodule ℂ (G → E) where
  carrier := {f | (∀ h ∈ H, ∀ g, f (g * h) = f g) ∧ ∀ g, f (γ * g) = T (f g)}
  add_mem' := by
    rintro f₁ f₂ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    exact ⟨fun h hh g => by simp [a₁ h hh g, a₂ h hh g], fun g => by simp [b₁ g, b₂ g]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, b⟩
    exact ⟨fun h hh g => by simp [a h hh g], fun g => by simp [b g]⟩

def rightInvRightTwisted (H : Subgroup G) (γ : G) (T : E →ₗ[ℂ] E) : Submodule ℂ (G → E) where
  carrier := {f | (∀ h ∈ H, ∀ g, f (g * h) = f g) ∧ ∀ g, f (g * γ) = T (f g)}
  add_mem' := by
    rintro f₁ f₂ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    exact ⟨fun h hh g => by simp [a₁ h hh g, a₂ h hh g], fun g => by simp [b₁ g, b₂ g]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, b⟩
    exact ⟨fun h hh g => by simp [a h hh g], fun g => by simp [b g]⟩

variable {H : Subgroup G} {γ : G} {T : E →ₗ[ℂ] E} {f : G → E}

end GlobalTheory.TwistedInverseSubgroups
