import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
  ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  first | exact @GlobalTheory.norm_surjective_of_is_c1 | exact GlobalTheory.norm_surjective_of_is_c1 | (intros; apply GlobalTheory.norm_surjective_of_is_c1 <;> assumption)
