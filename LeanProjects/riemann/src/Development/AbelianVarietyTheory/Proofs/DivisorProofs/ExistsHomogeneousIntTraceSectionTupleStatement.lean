import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIntTraceSectionTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_int_trace_sectionTuple : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (q : ℕ) (w : K), (∀ l, IsIntegral (ratR x l) (w / x l ^ q)) → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧ (Algebra.trace (ratF x) K (w / x 0 ^ q) : K) = aeval (fun l => x l / x 0) T := by
  first | exact @GlobalTheory.HSAmp.TraceHom.trace_homog | exact GlobalTheory.HSAmp.TraceHom.trace_homog | (intros; apply GlobalTheory.HSAmp.TraceHom.trace_homog <;> assumption)
