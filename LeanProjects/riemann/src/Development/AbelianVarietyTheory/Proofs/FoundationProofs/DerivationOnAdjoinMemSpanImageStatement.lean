import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImage
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationOn_adjoin_mem_span_image : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (s : Set S) (D : S → M), IsDerOn (Algebra.adjoin A s) D → ∀ x ∈ Algebra.adjoin A s, D x ∈ Submodule.span S (D '' s) := by
  first | exact @GlobalTheory.AlmostEt.derOn_adjoin_mem_span | exact GlobalTheory.AlmostEt.derOn_adjoin_mem_span | (intros; apply GlobalTheory.AlmostEt.derOn_adjoin_mem_span <;> assumption)
