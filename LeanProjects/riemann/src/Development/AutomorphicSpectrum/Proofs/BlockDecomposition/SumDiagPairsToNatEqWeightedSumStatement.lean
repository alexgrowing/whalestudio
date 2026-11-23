import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumDiagPairsToNatEqWeightedSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_diag_pairs_toNat_eq_weighted_sum : ∀ (n : ℕ) (x : Fin n → ℤ), StrictAnti x → ((∑ d ∈ Finset.range n, ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat : ℕ) : ℤ) = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.sum_diagPairs_toNat | exact GlobalTheory.CompanionTheory.IwJac.sum_diagPairs_toNat | (intros; apply GlobalTheory.CompanionTheory.IwJac.sum_diagPairs_toNat <;> assumption)
