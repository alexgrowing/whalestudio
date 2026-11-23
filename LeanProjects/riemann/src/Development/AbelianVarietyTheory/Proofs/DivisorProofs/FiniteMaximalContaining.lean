import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensitiesBoundedAlmostAll
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_maximal_containing : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  first | (exact @GlobalTheory.finite_maximal_ideals_containing') | (exact GlobalTheory.finite_maximal_ideals_containing') | (intros; apply GlobalTheory.finite_maximal_ideals_containing' <;> assumption)
