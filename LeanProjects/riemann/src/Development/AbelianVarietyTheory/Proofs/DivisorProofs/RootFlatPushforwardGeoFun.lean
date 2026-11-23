import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCoordinatesPPowerDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementsBoundedPadic
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AtP

theorem den_factorization_le {p : ℕ} (hp : p.Prime) (q : ℚ) (e : ℕ) (k : ℤ) (m : ℕ) (hm : ¬ p ∣ m)
    (h : q * (p : ℚ) ^ e = k / m) : q.den.factorization p ≤ e := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hq : q = Rat.divInt k ((m * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    have hp0 : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    rw [eq_div_iff (mul_ne_zero hm0' hp0), mul_comm (m : ℚ), ← mul_assoc, h, div_mul_cancel₀ _ hm0']
  have hd : q.den ∣ m * p ^ e := by
    have := Rat.den_dvd k ((m * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hne : m * p ^ e ≠ 0 := mul_ne_zero hm0 (pow_ne_zero _ hp.ne_zero)
  have := (Nat.factorization_le_iff_dvd (Rat.den_nz q) hne).2 hd p
  rw [Nat.factorization_mul hm0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, hp.factorization_pow, Finsupp.single_eq_same, zero_add] at this
  exact this

end GlobalTheory.AtP

namespace GlobalTheory.AtP

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (h₂ : Gr G 1), ∃ k : ℕ, ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization p ≤ k) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization p ≤ k := by
  intro p _ G β K' f' hf h₂
  have hp : p.Prime := Fact.out
  obtain ⟨B, e₁, hB⟩ := GlobalTheory.T.regular_elements_bounded_padic p G K' f' hf β h₂
  obtain ⟨e₂, he⟩ := GlobalTheory.T.bounded_coordinates_p_power_denominator p G B
  refine ⟨max e₁ e₂, fun y hy => ?_⟩
  obtain ⟨hb, k, m, hm, hs⟩ := hB y hy
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨k', m', hm', hc⟩ := he _ hb i
    exact (den_factorization_le hp _ e₂ k' m' hm' hc).trans (le_max_right _ _)
  · rw [Units.val_inv_eq_inv_val]
    exact (den_factorization_le hp _ e₁ k m hm hs).trans (le_max_left _ _)

end GlobalTheory.AtP
