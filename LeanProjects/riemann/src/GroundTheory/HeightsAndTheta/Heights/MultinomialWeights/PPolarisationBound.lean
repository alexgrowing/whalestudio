import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem prod_factorial_le_factorial_of_sum {σ : Type*} (m : σ →₀ ℕ) (n : ℕ)
    (hm : (m.sum fun _ e => e) = n) :
    (m.prod fun _ e => (e.factorial : ℝ)) ≤ (n.factorial : ℝ) := by
  have hd : (∏ i ∈ m.support, (m i).factorial) ∣ (∑ i ∈ m.support, m i).factorial :=
    Nat.prod_factorial_dvd_factorial_sum _ _
  have hle : (∏ i ∈ m.support, (m i).factorial) ≤ n.factorial := by
    rw [← hm]; exact Nat.le_of_dvd (Nat.factorial_pos _) hd
  show (∏ a ∈ m.support, ((m a).factorial : ℝ)) ≤ (n.factorial : ℝ)
  exact_mod_cast hle

theorem PolarisationBound.proof (hC : PolarisationCoeff.Statement) : PolarisationBound.Statement := by
  intro σ _ n
  refine ⟨fun Φ Ψ hΦΨ F hF => ?_, fun Φ m M hm hM => ?_⟩
  ·
    have hmono : ∀ m : σ →₀ ℕ, (m.sum fun _ e => e) = n → Φ (monomial m 1) = Ψ (monomial m 1) := by
      intro m hm
      rw [hC σ Φ n m hm, hC σ Ψ n m hm, hΦΨ]
    conv_lhs => rw [F.as_sum]
    conv_rhs => rw [F.as_sum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun m hmF => ?_)
    have hdeg : (m.sum fun _ e => e) = n := by
      have := hF (mem_support_iff.1 hmF)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    have hsm : monomial m (coeff m F) = coeff m F • monomial m (1 : ℝ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsm, map_smul, map_smul, hmono m hdeg]
  · have hc := hM m
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hc
    have hfac := prod_factorial_le_factorial_of_sum m n hm
    have hpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hpnn : (0 : ℝ) ≤ (m.prod fun _ e => (e.factorial : ℝ)) := by
      unfold Finsupp.prod
      exact Finset.prod_nonneg (fun _ _ => by positivity)
    have hq0 : 0 ≤ (m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ) := div_nonneg hpnn hpos.le
    have hq1 : (m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ) ≤ 1 := by
      rw [div_le_one hpos]; exact hfac
    rw [hC σ Φ n m hm, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hq0]
    calc (m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ) * |coeff m (polarPoly Φ n)|
        ≤ 1 * |coeff m (polarPoly Φ n)| :=
          mul_le_mul_of_nonneg_right hq1 (abs_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hc

end GroundTheory.Heights₂.Heights.TheoremB
