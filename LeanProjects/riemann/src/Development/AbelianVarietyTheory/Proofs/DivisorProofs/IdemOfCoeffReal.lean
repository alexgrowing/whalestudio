import Mathlib
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.LiftLat

open Formalism.L2.DIV

namespace GlobalTheory.CuspMult

theorem idemOf_coeff_real : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ)
    (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X →
    ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  intro K G _ _ _ σ X hX hS g
  rw [coeff_idemOf, map_sum, star_sum]
  refine Finset.sum_nbij' (fun χ t => χ t⁻¹) (fun χ t => χ t⁻¹) hS hS
    (fun χ _ => by simp) (fun χ _ => by simp) fun χ hχ => ?_
  have h1 := (hX χ hχ).map_inv σ 1
  have h2 := (hX χ hχ).map_inv σ g⁻¹
  simp only [map_mul, map_div₀, map_natCast, star_mul', star_div₀, star_natCast]
  rw [h1, h2]
  rfl

end GlobalTheory.CuspMult
