import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b c : B, b * c - 1 ∈ Ideal.span {f} → ∃ r : B, b - r ^ q ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed) | (exact GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed) | (intros; apply GlobalTheory.exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed  <;> assumption)
