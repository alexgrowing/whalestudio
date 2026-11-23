import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdPairSumsEqSumPowersetScore
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_pair_sums_eq_sum_powerset_score : ∀ {n : ℕ} (z : Fin n → ℂ), ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score | exact GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_pairs_add_eq_sum_score <;> assumption)
