import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedQuotientOfArtinianOfMaximalLe
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' : ∀ (A : Type) [CommRing A] (I : Ideal A), IsArtinianRing (A ⧸ I) →
    (∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) → IsReduced (A ⧸ I) := by
  first | (exact @GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (exact GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (intros; apply GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le  <;> assumption)
