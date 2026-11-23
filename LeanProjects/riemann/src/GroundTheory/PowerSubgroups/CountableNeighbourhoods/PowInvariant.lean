import Mathlib

namespace GroundTheory.Variant₂.N1

def mulZPowers (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ)) (s : Gal(AlgebraicClosure ℚ/ℚ))
    (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    Subgroup Gal(AlgebraicClosure ℚ/ℚ) where
  carrier := {x | ∃ k : ℤ, ∃ u ∈ U, x = s ^ k * u}
  one_mem' := ⟨0, 1, U.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, u, hu, rfl⟩ ⟨b, v, hv, rfl⟩
    refine ⟨a + b, s ^ (-b) * u * (s ^ (-b))⁻¹ * v, U.mul_mem (hU (-b) u hu) hv, ?_⟩
    rw [zpow_add, zpow_neg, inv_inv]
    group
  inv_mem' := by
    rintro _ ⟨k, u, hu, rfl⟩
    refine ⟨-k, s ^ k * u⁻¹ * (s ^ k)⁻¹, hU k _ (U.inv_mem hu), ?_⟩
    rw [zpow_neg]
    group

theorem le_powerSubgroup₂ (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    U ≤ mulZPowers U s hU := fun u hu => ⟨0, u, hu, by simp⟩

theorem mem_mulZPowers_self (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    s ∈ mulZPowers U s hU := ⟨1, 1, U.one_mem, by simp⟩

end GroundTheory.Variant₂.N1
