import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFibresAlmostAllOfSeparableDedekindCurve
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_fibres_almost_all_of_separable_dedekind_curve : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] (y : A), (Polynomial.aeval (R := k) y).Finite → Function.Injective (Polynomial.aeval (R := k) y) → Algebra.IsSeparable (IntermediateField.adjoin k {algebraMap A (FractionRing A) y}) (FractionRing A) → ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  first | (exact @GlobalTheory.reduced_fibres_almost_all_sep) | (exact GlobalTheory.reduced_fibres_almost_all_sep) | (intros; apply GlobalTheory.reduced_fibres_almost_all_sep  <;> assumption)
