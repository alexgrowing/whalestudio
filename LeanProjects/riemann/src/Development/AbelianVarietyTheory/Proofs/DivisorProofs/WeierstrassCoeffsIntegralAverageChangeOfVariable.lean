import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSlopeMemStatement

noncomputable section

open WeierstrassCurve
open scoped BigOperators

namespace GlobalTheory.CMModel

theorem avg_mem_of_card_unit (V : ValuationSubring ℂ) {ι : Type} [Fintype ι] (f : ι → ℂ)
    (hc : V.valuation (Fintype.card ι : ℂ) = 1) (hf : ∀ i, f i ∈ V) :
    (∑ i, f i) / Fintype.card ι ∈ V := by
  rw [div_eq_mul_inv]
  refine V.mul_mem _ _ (sum_mem (S := V) fun i _ => hf i) ?_
  rw [← V.valuation_le_one_iff, map_inv₀, hc, inv_one]

theorem intV_average (V : ValuationSubring ℂ) (a₄ a₆ r s t : ℂ) (u : ℂˣ) (ι : Type) [Fintype ι]
    (X Y : ι → ℂ)
    (h : IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)))
    (hc : V.valuation (Fintype.card ι : ℂ) = 1)
    (hX : ∀ i, (X i - r) / (u : ℂ) ^ 2 ∈ V)
    (hY : ∀ i, (Y i - t - s * (X i - r)) / (u : ℂ) ^ 3 ∈ V)
    (h2 : ∀ i, V.valuation (2 * Y i) = V.valuation (u : ℂ) ^ 3) :
    IntV V ((⟨u, (∑ i, X i) / Fintype.card ι,
      (∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)) / Fintype.card ι,
      (∑ i, Y i) / Fintype.card ι⟩ : VariableChange ℂ) •
      (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact zero_ne_one hc
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hr := avg_mem_of_card_unit V _ hc hX
  have ht := avg_mem_of_card_unit V _ hc hY
  have hs := avg_mem_of_card_unit V _ hc fun i =>
    GlobalTheory.T.tangent_slope_mem_of_intV V a₄ a₆ r s t (X i) (Y i) u h (hX i) (hY i) (h2 i)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hr hs ht
  set A := ∑ i, X i
  set B := ∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)
  set D := ∑ i, Y i
  set n : ℂ := ((Fintype.card ι : ℕ) : ℂ)
  have key : (⟨u, A / n, B / n, D / n⟩ : VariableChange ℂ) =
      (⟨1, (A - n * r) / (u : ℂ) ^ 2 / n, (B - n * s) / (u : ℂ) / n,
        (D - n * t - s * (A - n * r)) / (u : ℂ) ^ 3 / n⟩ : VariableChange ℂ) * ⟨u, r, s, t⟩ := by
    rw [VariableChange.mul_def]
    ext
    · simp
    all_goals
      simp only []
      field_simp
      ring
  rw [key, mul_smul]
  exact GlobalTheory.coeff_mem_variableChange V.toSubring h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hr hs ht rfl

end GlobalTheory.CMModel
