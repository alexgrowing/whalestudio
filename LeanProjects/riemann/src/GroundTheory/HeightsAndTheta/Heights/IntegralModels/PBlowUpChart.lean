import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open IsLocalRing

theorem BlowUpChart.proof : BlowUpChart.Statement := by
  intro A _ _ _ _ K _ _ _ n x hx ⟨j, hj⟩
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A K)
  set f := (algebraMap A K).codRestrict V.toSubring hV with hf
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun k => V.valuation (algebraMap A K (x k))
  have hinj := IsFractionRing.injective A K
  have hxi : x i ≠ 0 := by
    intro h0
    apply hj
    have h1 := hi j
    rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (by rw [h1, map_zero])
  have hvi : 0 < V.valuation (algebraMap A K (x i)) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact fun h => hxi (hinj (by rw [h, map_zero]))
  have hle : ∀ y ∈ blowUpChart K x i, y ∈ V := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hvi]
      exact hi k
    | algebraMap r => exact hV r
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
  let φ : blowUpChart K x i →+* V :=
    { toFun := fun y => ⟨y.1, hle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ a : A, φ (algebraMap A (blowUpChart K x i) a) = f a := fun _ => rfl
  have hxm : x i ∈ maximalIdeal A := hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have hnu : ¬ IsUnit (f (x i)) := by
    rw [isUnit_map_iff f]
    exact hxm
  refine ⟨i, hxi, fun hu => hnu (hφ (x i) ▸ hu.map φ), (maximalIdeal V).comap φ,
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · rw [Ideal.mem_comap, hφ]
    exact hnu
  · ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ, mem_maximalIdeal, mem_nonunits_iff,
      mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff f]

end GroundTheory.Heights₂.Heights.Model
