import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemidirectProductHomeomorphOfClosedComplement
import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q), IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | exact GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | (intros; apply GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements <;> assumption)
