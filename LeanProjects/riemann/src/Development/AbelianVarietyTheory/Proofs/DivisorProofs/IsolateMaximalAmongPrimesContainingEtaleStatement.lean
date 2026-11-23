import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolateMaximalAmongPrimesContainingEtale
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isolate_maximal_among_primes_containing_etale : ∀ (B D : Type) [CommRing B] [IsDedekindDomain B] [CommRing D] [Algebra B D] [Algebra.Etale B D] (f : B), f ≠ 0 → ∀ (Q : Ideal D), Q.IsMaximal → ∃ g : D, g ∉ Q ∧ ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q := by
  first | (exact @GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing) | (exact GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing) | (intros; apply GlobalTheory.EtaleIsolate.isolate_maximal_among_primes_containing  <;> assumption)
