import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DivMono

theorem coeff_finsuppProd_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (σ τ : Type) (u : τ → MvPowerSeries σ R), (∀ j, constantCoeff (u j) = 0) →
      ∀ (α : τ →₀ ℕ) (β : σ →₀ ℕ), β.degree < α.degree → coeff β (α.prod fun j e => u j ^ e) = 0 := by
  intro R _ σ τ u hu α β hβ
  apply coeff_of_lt_order
  have hle : ((α.degree : ℕ) : ℕ∞) ≤ (α.prod fun j e => u j ^ e).order := by
    unfold Finsupp.prod
    refine le_trans ?_ (le_order_prod (fun j => u j ^ α j) α.support)
    rw [Finsupp.degree_apply, Nat.cast_sum]
    exact Finset.sum_le_sum fun j _ => le_order_pow_of_constantCoeff_eq_zero (α j) (hu j)
  exact lt_of_lt_of_le (by exact_mod_cast hβ) hle

end GlobalTheory.DivMono
