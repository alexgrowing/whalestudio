import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGe

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_le_rev_eq_prod_ge : ∀ {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h), ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a) = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  first | exact @GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev | exact GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev | (intros; apply GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev <;> assumption)
