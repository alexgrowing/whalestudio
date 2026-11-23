import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

private lemma twelfth_power_clear_denom_three_mod_eight (p : ℕ) (D A Q s : ℂ) (n : ℕ) (hp0 : (p:ℂ) ≠ 0) (hD0 : D ≠ 0)
    (hQ0 : Q ≠ 0) (hs2 : s^2 = 1) (hε : Q^4 * (p:ℂ)^3 = s * D^(4*n+1)) :
    (A*D^n/(Q*p))^12 * (p:ℂ)^3 * D^3 * s = A^12 := by
  have h3 : Q^12 * (p:ℂ)^9 = s * D^(12*n+3) := by
    calc Q^12 * (p:ℂ)^9 = (Q^4 * (p:ℂ)^3)^3 := by ring
      _ = s^2 * s * D^(12*n+3) := by rw [hε]; ring
      _ = _ := by rw [hs2]; ring
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_iff (by positivity)]
  linear_combination (-(A^12 * (p:ℂ)^3)) * h3

private lemma twelfth_power_clear_denom_seven_mod_eight (p : ℕ) (D A Q s : ℂ) (n : ℕ) (hD0 : D ≠ 0)
    (hs2 : s^2 = 1) (hε : Q^4 * (p:ℂ)^3 = s * D^(4*n+3)) :
    (A*Q/D^(n+1))^12 * (p:ℂ)^9 * D^3 * s = A^12 := by
  have h3 : Q^12 * (p:ℂ)^9 = s * D^(12*n+9) := by
    calc Q^12 * (p:ℂ)^9 = (Q^4 * (p:ℂ)^3)^3 := by ring
      _ = s^2 * s * D^(12*n+9) := by rw [hε]; ring
      _ = _ := by rw [hs2]; ring
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_iff (by positivity)]
  linear_combination (A^12 * D^3 * s) * h3 + (A^12 * D^(12*n+12)) * hs2

private lemma twelfth_cancel (V : ValuationSubring ℂ) (D A u P s : ℂ) (e : ℕ) (hD0 : D ≠ 0)
    (hs2 : s^2 = 1) (hv : V.valuation A ^ 3 = V.valuation D)
    (h : u^12 * P^e * D^3 * s = A^12) :
    V.valuation u ^ 12 * V.valuation P ^ e = V.valuation D := by
  have hs : V.valuation s = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs2.trans (one_pow 2).symm) with h1 | h1 <;>
      simp [h1]
  have h' := congrArg V.valuation h
  simp only [map_mul, map_pow, hs, mul_one] at h'
  have hD' : V.valuation D ^ 3 ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 hD0)
  apply mul_right_cancel₀ hD'
  rw [h', show 12 = 3 * 4 from rfl, pow_mul, hv, ← pow_succ']

theorem valuation_twelfth_power_of_cube :
    ∀ (p : ℕ) (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (D A Q : ℂ), p % 4 = 3 →
      D ∈ F → A ∈ F → Q ∈ F → D ≠ 0 → A ≠ 0 → V.valuation A ^ 3 = V.valuation D →
      Q ^ 8 * (p : ℂ) ^ 6 = D ^ (p - 1) →
      ∃ u ∈ F, u ≠ 0 ∧ V.valuation u ^ 12 * V.valuation (p : ℂ) ^ (if p % 8 = 3 then 3 else 9)
        = V.valuation D := by
  intro p V F D A Q hp hD hA hQ hD0 hA0 hv hrel
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [show p - 1 = 2 * (2 * k + 1) by omega, pow_mul'] at hrel
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hrel
    exact pow_ne_zero _ (pow_ne_zero _ hD0) hrel.symm
  have hsq : (Q^4 * (p:ℂ)^3)^2 = (D^(2*k+1))^2 := by rw [← hrel]; ring
  obtain ⟨s, hs2, hε⟩ : ∃ s : ℂ, s^2 = 1 ∧ Q^4 * (p:ℂ)^3 = s * D^(2*k+1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨1, by norm_num, by rw [h, one_mul]⟩
    · exact ⟨-1, by norm_num, by rw [h, neg_one_mul]⟩
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rw [show 2 * (2 * n) + 1 = 4 * n + 1 by ring] at hε
    refine ⟨A * D^n / (Q * p), div_mem (mul_mem hA (pow_mem hD n)) (mul_mem hQ (natCast_mem F p)),
      div_ne_zero (mul_ne_zero hA0 (pow_ne_zero _ hD0)) (mul_ne_zero hQ0 hp0), ?_⟩
    rw [if_pos (by omega)]
    exact twelfth_cancel V D A _ _ s 3 hD0 hs2 hv (twelfth_power_clear_denom_three_mod_eight p D A Q s n hp0 hD0 hQ0 hs2 hε)
  · rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by ring] at hε
    refine ⟨A * Q / D^(n+1), div_mem (mul_mem hA hQ) (pow_mem hD _),
      div_ne_zero (mul_ne_zero hA0 hQ0) (pow_ne_zero _ hD0), ?_⟩
    rw [if_neg (by omega)]
    exact twelfth_cancel V D A _ _ s 9 hD0 hs2 hv (twelfth_power_clear_denom_seven_mod_eight p D A Q s n hD0 hs2 hε)

end GlobalTheory
