import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almostDualTrace_derivation_mem_span_values : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → ∀ x ∈ C, (e * e) • D x ∈ Submodule.span S (D '' (B : Set S)) := by
  first | exact @GlobalTheory.AlmostEt.derOn_mem_span_of_trData | exact GlobalTheory.AlmostEt.derOn_mem_span_of_trData | (intros; apply GlobalTheory.AlmostEt.derOn_mem_span_of_trData <;> assumption)
