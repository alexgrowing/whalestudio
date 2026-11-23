import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurve
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squarefree_poly_distinct_zeros_on_curve : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  first | exact @GlobalTheory.SquarefreeFibre.main | exact GlobalTheory.SquarefreeFibre.main | (intros; apply GlobalTheory.SquarefreeFibre.main <;> assumption)
