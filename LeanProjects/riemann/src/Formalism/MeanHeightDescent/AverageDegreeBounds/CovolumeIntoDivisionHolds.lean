import Mathlib
import Formalism.MeanHeightDescent.StatementA

open Finset

namespace Formalism.ExtensionFiltration

theorem descent_numeric : DescentNumeric := by
  intro dA dB muA muN cfl X P Λ Q ε hdA hAB hBε hε hX hP hdeg hmuA hcfl hΛ
  have hdB : 0 < dB := lt_of_lt_of_le hdA hAB
  have hQ : 0 ≤ Q := le_trans (abs_nonneg _) hcfl
  have hc1 : cfl ≤ Q := le_trans (le_abs_self _) hcfl

  by_contra hcon
  rw [not_le] at hcon
  have h1 : dB * muN < dB * (cfl - X - P - 2 * ε * Q) := mul_lt_mul_of_pos_left hcon hdB
  have h2 : dA * (cfl - X - P) ≤ dA * (muA - P) := by
    apply mul_le_mul_of_nonneg_left _ hdA.le; linarith
  have h3 : (dB - dA) * (-Q) ≤ (dB - dA) * (-Λ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
  have h4 : (dB - dA) * (cfl - X - P) ≤ (dB - dA) * Q := by
    apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
  have h5 : (dB - dA) * Q ≤ ε * dB * Q := by
    apply mul_le_mul_of_nonneg_right _ hQ; linarith
  nlinarith

theorem bad_part_numeric : BadRowsNumeric := by
  intro d dg db muN muG mmax G Q δ hd hsum hdb hdb3 hδ hδ12 hdeg hmuN hmm hG
  have hQ : 0 ≤ Q := le_trans (abs_nonneg _) hmuN
  have hN1 : -Q ≤ muN := by have := neg_abs_le muN; linarith
  have hdg : 3 / 4 * d ≤ dg := by nlinarith
  have hdg0 : 0 < dg := by linarith
  by_contra hcon
  rw [not_le] at hcon
  have h1 : dg * muG < dg * (muN - 12 * δ * Q) := mul_lt_mul_of_pos_left hcon hdg0
  have h2 : db * (mmax + G) ≤ db * (2 * Q) := by
    apply mul_le_mul_of_nonneg_left _ hdb; linarith
  have h3 : db * (-muN) ≤ db * Q := by
    apply mul_le_mul_of_nonneg_left _ hdb; linarith
  have h4 : db * Q ≤ 3 * δ * d * Q := mul_le_mul_of_nonneg_right hdb3 hQ
  have h5 : 3 / 4 * d * (δ * Q) ≤ dg * (δ * Q) :=
    mul_le_mul_of_nonneg_right hdg (mul_nonneg hδ hQ)
  subst hsum
  nlinarith

theorem slope_lower_chain_holds : SlopeLowerChain := by
  intro Pl _ w c1 ua muU muA muN muG muM mmax dA dB d dg db C1 Cf LL0 L b rd m q' cfl ε δ Q P Λ G P9
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hC1 hCf hq0 hqm hw hua hrd0 hrdL hLL hU hb
  have hLL0 : 0 ≤ LL0 := le_trans hrd0 hrdL
  have hU0 : 0 ≤ ∑ τ, ua τ := by linarith
  have hX : 0 ≤ 2 * (C1 * LL0 * (∑ τ, ua τ) + b / 4) := by positivity
  have hN := descent_numeric dA dB muA muN (2 * cfl) (2 * (C1 * LL0 * (∑ τ, ua τ) + b / 4)) P Λ Q ε
    hdA hAB hBε hε hX hP hdesc (by linarith) hcQ hΛ
  have hGd := bad_part_numeric d dg db muN muG mmax G Q δ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG
  have hW0 : 0 ≤ ∑ τ, w τ := Finset.sum_nonneg (fun τ _ => hw τ)
  have hmW : m * (∑ τ, w τ) ≤ 2 * ∑ τ, ua τ := by
    have : ∑ τ, m * w τ / 2 ≤ ∑ τ, ua τ := Finset.sum_le_sum (fun τ _ => hua τ)
    rw [← Finset.sum_div, ← Finset.mul_sum] at this
    linarith
  have hqW : q' * (∑ τ, w τ) ≤ 2 * ∑ τ, ua τ :=
    le_trans (mul_le_mul_of_nonneg_right hqm hW0) hmW
  have h1 : Real.log rd * (q' * (∑ τ, w τ)) ≤ LL0 * (2 * ∑ τ, ua τ) :=
    mul_le_mul hrdL hqW (mul_nonneg hq0 hW0) hLL0
  have h2 : L ≤ LL0 * (∑ τ, ua τ) := by nlinarith
  have h3 : Cf * (Real.log rd * (q' * (∑ τ, w τ))) ≤ Cf * (LL0 * (2 * ∑ τ, ua τ)) :=
    mul_le_mul_of_nonneg_left h1 hCf
  have h4 : Cf * L ≤ Cf * (LL0 * (∑ τ, ua τ)) := mul_le_mul_of_nonneg_left h2 hCf
  nlinarith

end Formalism.ExtensionFiltration
