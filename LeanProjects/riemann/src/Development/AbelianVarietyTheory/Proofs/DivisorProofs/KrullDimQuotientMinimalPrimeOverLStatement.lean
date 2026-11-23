import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_dim_quotient_minimal_prime_over_l : ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] (l : ℕ) [Fact l.Prime] (q : Ideal A) [q.IsPrime], q ∈ (Ideal.span {(l : A)}).minimalPrimes → ∀ d : ℕ, Algebra.trdeg ℤ A = d → ringKrullDim (A ⧸ q) = d := by
  first | exact @GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime | exact GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime | (intros; apply GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime <;> assumption)
