import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem cochain_coboundary_prod_hom_identities :
    ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
    (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
    η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
    (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  intro Γ _ N x y η h
  refine ⟨?_, ?_, ?_⟩
  · have h0 := h 1 1
    simp only [map_one, toAdd_one, zero_mul, mul_one] at h0
    linear_combination -h0
  · intro g n
    have h1 := h g n
    have h2 := h (g * n * g⁻¹) g
    have e : g * n * g⁻¹ * g = g * n := by group
    have e2 : (x (g * n * g⁻¹)).toAdd = (x n).toAdd := by
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
      ring
    rw [e, e2] at h2
    linear_combination h1 - h2
  · intro m n hm
    have h3 := h m n
    rw [hm, zero_mul] at h3
    linear_combination h3

end GlobalTheory
