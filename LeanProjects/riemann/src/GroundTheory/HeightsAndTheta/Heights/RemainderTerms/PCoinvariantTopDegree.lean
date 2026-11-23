import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem Coinv.monomial_staircase_eq (f N : ℕ) :
    (monomial (Coinv.staircase f N) (1 : ℚ) : RootRing f N) =
      ∏ τ : Fin f, ∏ i : Fin N, X (τ, i) ^ (i : ℕ) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  simp [Coinv.staircase]

theorem Coinv.psumIdeal_rat_eq (f N : ℕ) :
    Coinv.psumIdeal ℚ f N =
      Ideal.span {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = blockPowerSum f N k τ} := rfl

theorem CoinvariantTopDegree.proof (h1 : CoinvAtTop.Statement) : CoinvariantTopDegree.Statement := by
  intro f N H hH
  obtain ⟨c, hc⟩ := h1 ℚ f N H hH
  refine ⟨c, ?_⟩
  rw [← Coinv.monomial_staircase_eq, ← Coinv.psumIdeal_rat_eq]
  exact hc

end

end GroundTheory.Heights₂.Heights.RestTerms
