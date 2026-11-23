import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem loc_split {X M' : Type} [Group X] [Group M'] (L' : Loc X M') {K : Subgroup X} {Kw : Subgroup M'}
    (hF : L'.Fact K Kw) {k : X} (hk : k ∈ K) :
    ∃ a ∈ Kw, ∃ k₀ ∈ K, L'.pr k₀ = 1 ∧ k = L'.loc a * k₀ := by
  refine ⟨L'.pr k, hF.2 k hk, (L'.loc (L'.pr k))⁻¹ * k, K.mul_mem (K.inv_mem (hF.1 _ (hF.2 k hk))) hk, ?_, by group⟩
  simp [L'.pr_loc]

private theorem loc_key {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (a t b : M') {k₀ r k₁ : X}
    (h₀ : L'.pr k₀ = 1) (hr : L'.pr r = 1) (h₁ : L'.pr k₁ = 1) :
    L'.loc a * k₀ * (L'.loc t * r) * (k₁ * L'.loc b) = L'.loc (a * t * b) * (k₀ * r * k₁) := by
  have hprod : L'.pr (k₀ * r * k₁) = 1 := by simp [map_mul, h₀, hr, h₁]
  have e1 := L'.comm t k₀ h₀
  have e2 := L'.comm b (k₀ * r * k₁) hprod
  rw [map_mul, map_mul]
  calc L'.loc a * k₀ * (L'.loc t * r) * (k₁ * L'.loc b)
      = L'.loc a * (k₀ * L'.loc t) * r * k₁ * L'.loc b := by group
    _ = L'.loc a * (L'.loc t * k₀) * r * k₁ * L'.loc b := by rw [e1]
    _ = L'.loc a * L'.loc t * ((k₀ * r * k₁) * L'.loc b) := by group
    _ = L'.loc a * L'.loc t * L'.loc b * (k₀ * r * k₁) := by rw [← e2]; group

theorem UpperTheory.Gal.W2.Seed.pDosetIff :
    ∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K := by
  intro X M' _ _ L' K Kw hF t r hr g
  constructor
  · intro hg
    rw [DoubleCoset.mem_doubleCoset] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    obtain ⟨a, ha, k₀, hk₀, h₀, rfl⟩ := loc_split L' hF hx
    obtain ⟨b, hb, k₁, hk₁, h₁, rfl⟩ := loc_split L' hF hy
    have hc : L'.loc b * k₁ = k₁ * L'.loc b := L'.comm b k₁ h₁
    rw [hc, loc_key L' a t b h₀ hr h₁]
    have hpr : L'.pr (L'.loc (a * t * b) * (k₀ * r * k₁)) = a * t * b := by
      simp [map_mul, h₀, hr, h₁, L'.pr_loc]
    rw [hpr]
    refine ⟨?_, ?_⟩
    · rw [DoubleCoset.mem_doubleCoset]
      exact ⟨a, ha, b, hb, rfl⟩
    · rw [DoubleCoset.mem_doubleCoset, inv_mul_cancel_left]
      exact ⟨k₀, hk₀, k₁, hk₁, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [DoubleCoset.mem_doubleCoset] at h1 h2 ⊢
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    obtain ⟨k₀, hk₀, k₁, hk₁, hk⟩ := h2
    have hg : g = L'.loc (L'.pr g) * (k₀ * r * k₁) := by
      rw [← hk]
      group
    have hpg := congrArg L'.pr hg
    simp only [map_mul, L'.pr_loc, hr, mul_one] at hpg
    have hpk : L'.pr k₀ * L'.pr k₁ = 1 := by
      calc L'.pr k₀ * L'.pr k₁ = (L'.pr g)⁻¹ * (L'.pr g * (L'.pr k₀ * L'.pr k₁)) := by group
        _ = 1 := by rw [← hpg]; group
    have hcr := L'.comm (L'.pr k₀) r hr
    have hk0 : L'.pr (k₀ * (L'.loc (L'.pr k₀))⁻¹) = 1 := by
      simp [map_mul, map_inv, L'.pr_loc]
    have hk1 : L'.pr (L'.loc (L'.pr k₀) * k₁) = 1 := by
      rw [map_mul, L'.pr_loc, hpk]
    have hsplit : k₀ * r * k₁ =
        k₀ * (L'.loc (L'.pr k₀))⁻¹ * r * (L'.loc (L'.pr k₀) * k₁) := by
      calc k₀ * r * k₁ = k₀ * (L'.loc (L'.pr k₀))⁻¹ * (L'.loc (L'.pr k₀) * r) * k₁ := by group
        _ = _ := by rw [hcr]; group
    refine ⟨L'.loc a * (k₀ * (L'.loc (L'.pr k₀))⁻¹), ?_, L'.loc (L'.pr k₀) * k₁ * L'.loc b, ?_, ?_⟩
    · exact K.mul_mem (hF.1 a ha) (K.mul_mem hk₀ (K.inv_mem (hF.1 _ (hF.2 _ hk₀))))
    · exact K.mul_mem (K.mul_mem (hF.1 _ (hF.2 _ hk₀)) hk₁) (hF.1 b hb)
    · rw [loc_key L' a t b hk0 hr hk1, ← hab, ← hsplit]
      exact hg
