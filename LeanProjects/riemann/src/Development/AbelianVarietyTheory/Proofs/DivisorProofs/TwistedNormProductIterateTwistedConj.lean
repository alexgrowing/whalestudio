import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem nrmG_succ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ : H) :
    nrmG θ (r + 1) δ = nrmG θ r δ * (⇑θ)^[r] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem iter_hom_mul {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x y : H) :
    (⇑θ)^[r] (x * y) = (⇑θ)^[r] x * (⇑θ)^[r] y := by
  induction r generalizing x y with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_mul, ih]

theorem iter_hom_inv {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x : H) :
    (⇑θ)^[r] x⁻¹ = ((⇑θ)^[r] x)⁻¹ := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_inv, ih]

theorem nrmG_twConj {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H) :
    nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧
      δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  induction r with
  | zero => simp [nrmG]
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [nrmG_succ, nrmG_succ, h1, iter_hom_mul, iter_hom_mul,
        iter_hom_inv, Function.iterate_succ_apply]
      group
    · rw [nrmG_succ, map_mul, ← mul_assoc, h2, mul_assoc, ← Function.iterate_succ_apply' (⇑θ), mul_assoc]

end GlobalTheory.LKMid
