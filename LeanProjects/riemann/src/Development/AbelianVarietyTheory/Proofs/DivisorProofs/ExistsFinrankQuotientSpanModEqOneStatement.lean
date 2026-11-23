import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinrankQuotientSpanModEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finrank_quotient_span_mod_eq_one' : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 1 ≤ N → ∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
  first | exact @GlobalTheory.exists_finrank_quotient_span_mod_eq_one | exact GlobalTheory.exists_finrank_quotient_span_mod_eq_one | (intros; apply GlobalTheory.exists_finrank_quotient_span_mod_eq_one <;> assumption)
