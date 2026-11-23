import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

private theorem natCast_mul_act_mem_range_intCast (c : ℕ) (z : Fin 2 → ℚ) (δ : SL(2, ℤ))
    (h0 : (c : ℚ) * z 0 ∈ Set.range ((↑) : ℤ → ℚ)) (h1 : (c : ℚ) * z 1 ∈ Set.range ((↑) : ℤ → ℚ))
    (i : Fin 2) : (c : ℚ) * act z δ i ∈ Set.range ((↑) : ℤ → ℚ) := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  refine ⟨a * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 i + b * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 i, ?_⟩
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [ha, hb]
  ring

private theorem act_act_inv' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act (act x γ) γ⁻¹ = x := by
  have hd := γ.2
  rw [Matrix.det_fin_two] at hd
  have hq : ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) : ℚ) = 1 := by
    rw [hd]; simp
  push_cast at hq
  funext i
  fin_cases i <;>
    simp [act, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;>
    push_cast
  · linear_combination x 0 * hq
  · linear_combination x 1 * hq

theorem admissible_act_SL2 : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → admitted c (act x γ) := by
  rintro c x γ ⟨h1, h2, h3⟩
  refine ⟨h1, h2, fun ⟨k0, k1⟩ => h3 ?_⟩
  rw [← act_act_inv' x γ]
  exact ⟨natCast_mul_act_mem_range_intCast c _ _ k0 k1 0, natCast_mul_act_mem_range_intCast c _ _ k0 k1 1⟩

end GlobalTheory.Sieg
