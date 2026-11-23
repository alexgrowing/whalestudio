import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Torsfree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cardsep

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.mink3 :
    ∀ (R : Type) [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R] (H : Subgroup Rˣ), Finite H →
    Nat.card H ≤ 3 ^ Module.finrank ℤ R := by
  intro R _ _ _ H hH
  let f : H → R := fun h => ((h : Rˣ) : R)
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Units.ext hab)
  have hsep : ∀ a ∈ Set.range f, ∀ b ∈ Set.range f, ∀ x : R, a - b = (3 : ℕ) • x → a = b := by
    rintro _ ⟨h1, rfl⟩ _ ⟨h2, rfl⟩ x hx
    have ha : f h1 = f h2 + 3 * x := by
      rw [sub_eq_iff_eq_add'] at hx
      rw [hx, nsmul_eq_mul, Nat.cast_ofNat]
    let u : H := h2⁻¹ * h1
    have hu : f u = 1 + 3 * (f h2⁻¹ * x) := by
      have e : f u = f h2⁻¹ * f h1 := by
        simp [f, u]
      have e2 : f h2⁻¹ * f h2 = 1 := by
        simp [f]
      rw [e, ha, mul_add, e2]
      congr 1
      noncomm_ring
    have hpow : f u ^ orderOf u = 1 := by
      have : u ^ orderOf u = 1 := pow_orderOf_eq_one u
      simp only [f]
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, this]
      rfl
    have h1u := UpperTheory.V.KT.torsfree R (f u) _ (orderOf u) (orderOf_pos u) hu hpow
    have hu1 : u = 1 := hinj (by rw [h1u]; simp [f])
    have : h2 = h1 := inv_mul_eq_one.mp hu1
    rw [this]
  obtain ⟨_, hcard⟩ := UpperTheory.V.KT.cardsep R 3 (by norm_num) (Set.range f) hsep
  rw [Set.ncard_range_of_injective hinj] at hcard
  exact hcard
