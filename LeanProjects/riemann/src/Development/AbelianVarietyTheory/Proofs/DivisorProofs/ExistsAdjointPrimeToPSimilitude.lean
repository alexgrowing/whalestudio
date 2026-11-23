import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_adjoint_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : D.La →ₗ[D.O] D.La) (c k : ℕ),
    c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) →
    c ∣ k ^ 2 → ∃ g' : D.La →ₗ[D.O] D.La, (∀ x, g (g' x) = k • x) ∧ (∀ x, g' (g x) = k • x) ∧
      (∀ x y, D.EF (g' x) (g' y) = (k ^ 2 / c) * D.EF x y) ∧ (∀ x, ∃ y, g' y = k • x) ∧
      (k ^ 2 / c).Coprime p ∧ (k ^ 2 / c) ∣ k ^ 2 ∧ c * (k ^ 2 / c) = k ^ 2 := by
  intro p _ D g c k hc hk hE himg hck
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hp1 (by simpa using hc)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hp1 (by simpa using hk)
  have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0

  have ginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply D.nondeg
    ext y
    have h := hE x y
    rw [hx, map_zero, LinearMap.zero_apply] at h
    simp only [map_zero, LinearMap.zero_apply]
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hcZ
    · exact h'
  choose f hf using himg
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y => ginj (by rw [map_add, hf, hf, hf, smul_add])
  have fsmul : ∀ (b : D.O) x, f (b • x) = b • f x := fun b x => ginj (by
    rw [map_smul, hf, hf, smul_comm])
  let g' : D.La →ₗ[D.O] D.La :=
    { toFun := f, map_add' := fadd, map_smul' := fsmul }
  have h1 : ∀ x, g (g' x) = k • x := hf
  have h2 : ∀ x, g' (g x) = k • x := fun x => ginj (by rw [h1, map_nsmul])
  obtain ⟨q, hq⟩ := hck
  have hdiv : k ^ 2 / c = q := by rw [hq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hc0)]
  refine ⟨g', h1, h2, ?_, fun x => ⟨g x, h2 x⟩, ?_, ?_, ?_⟩
  · intro x y
    have h := hE (g' x) (g' y)
    rw [h1, h1, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul] at h
    push_cast [hdiv]
    have hqZ : ((k : ℤ) ^ 2 / c) = q := by
      rw [show (k : ℤ) ^ 2 = ((k ^ 2 : ℕ) : ℤ) by push_cast; ring, hq]
      push_cast
      exact Int.mul_ediv_cancel_left _ hcZ
    have hqI : (k : ℤ) ^ 2 = c * q := by exact_mod_cast hq
    rw [hqZ]
    apply mul_left_cancel₀ hcZ
    rw [← h, nsmul_eq_mul]
    push_cast
    rw [← sq, hqI]
    ring
  · rw [hdiv]
    have : q ∣ k ^ 2 := ⟨c, by rw [hq, mul_comm]⟩
    exact Nat.Coprime.coprime_dvd_left this (Nat.Coprime.pow_left 2 hk)
  · rw [hdiv]; exact ⟨c, by rw [hq, mul_comm]⟩
  · rw [hdiv, hq]

end GlobalTheory.UPel.HT.Hecke
