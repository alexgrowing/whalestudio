import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.RpOfIsIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneP

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.NO

theorem key_id {F : Type} [Field F] (B B' d : F) (hβ : 1 - B - d ≠ 0) (hβ' : 1 - B' - d ≠ 0) :
    (1 + d / (1 - B - d)) * (1 + d / (1 - B' - d)) * (1 - 2 * d)
      - (1 + d / (1 - B - d)) * (d / (1 - B' - d)) * B'
      - (d / (1 - B - d)) * (1 + d / (1 - B' - d)) * B
      + (d / (1 - B - d)) * (d / (1 - B' - d)) = 1 := by
  field_simp
  ring

theorem hf_comb {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (a b : K) (e v : ι → K) :
    hf c (a • e - b • v) (a • e - b • v) = a * c a * hf c e e - a * c b * hf c e v
      - b * c a * hf c v e + b * c b * hf c v v := by
  have h : ∀ i, (a * e i - b * v i) * c (a * e i - b * v i) = a * c a * (e i * c (e i))
      - a * c b * (e i * c (v i)) - b * c a * (v i * c (e i)) + b * c b * (v i * c (v i)) := by
    intro i; simp only [map_sub, map_mul]; ring
  simp only [hf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem refl_norm {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) {ι : Type} [Fintype ι]
    {e' v₀ : ι → K} {d β η : K} (hv : hf c v₀ v₀ = 1) (hu : hf c e' e' = 1 - 2 * d) (hd : c d = d)
    (hβ : β = 1 - hf c v₀ e' - d) (hβ0 : β ≠ 0) (hη : η = d / β) :
    hf c ((1 + η) • e' - η • v₀) ((1 + η) • e' - η • v₀) = 1 := by
  subst hβ hη
  have hcβ : c (1 - hf c v₀ e' - d) = 1 - c (hf c v₀ e') - d := by
    rw [map_sub, map_sub, map_one, hd]
  have hβ' : 1 - c (hf c v₀ e') - d ≠ 0 := by
    intro h; apply hβ0; rw [← hc (1 - hf c v₀ e' - d), hcβ, h, map_zero]
  have hcη : c (d / (1 - hf c v₀ e' - d)) = d / (1 - c (hf c v₀ e') - d) := by
    rw [map_div₀, hd, hcβ]
  have hca : c (1 + d / (1 - hf c v₀ e' - d)) = 1 + d / (1 - c (hf c v₀ e') - d) := by
    rw [map_add, map_one, hcη]
  rw [hf_comb, hca, hcη, hu, hv, hf_symm c hc v₀ e', mul_one]
  exact key_id _ _ d hβ0 hβ'

theorem pick {F : Type} [Field F] (X Y r : F) (h1 : r ≠ 1) (h2 : r ^ 2 ≠ 1) (h3 : r ≠ r ^ 2) :
    (X ≠ 1 ∧ Y ≠ 1) ∨ (r * X ≠ 1 ∧ Y ≠ r) ∨ (r ^ 2 * X ≠ 1 ∧ Y ≠ r ^ 2) := by
  by_cases hA : X ≠ 1 ∧ Y ≠ 1
  · exact Or.inl hA
  by_cases hB : r * X ≠ 1 ∧ Y ≠ r
  · exact Or.inr (Or.inl hB)
  rw [not_and_or, not_not, not_not] at hA hB
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · intro hX2
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · apply h1; rw [hA, mul_one] at hB; exact hB
    · apply h2; rw [hA, mul_one] at hX2; exact hX2
    · apply h1
      have : r ^ 2 * X = r * (r * X) := by ring
      rw [this, hB, mul_one] at hX2; exact hX2
    · apply h1; rw [← hB, hA]
  · intro hY2
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · apply h1; rw [hA, mul_one] at hB; exact hB
    · exact h3 (hB.symm.trans hY2)
    · apply h2; rw [← hY2, hA]
    · apply h2; rw [← hY2, hA]

end PI.KLW.NO
