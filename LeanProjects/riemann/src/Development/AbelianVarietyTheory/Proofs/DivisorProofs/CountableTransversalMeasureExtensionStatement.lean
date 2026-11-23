import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableTransversalMeasureExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countable_transversal_measure_extension : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q R : Subgroup G) [Countable R], IsClosed (N : Set G) → (∀ h ∈ Q ⊔ N, ∃ r ∈ R, r * h ∈ N) → ∀ (νN : Measure N) (ν : Measure ↥(Q ⊔ N)), (∀ A : Set N, ν (Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) '' A) = νN A) → (∀ h : ↥(Q ⊔ N), MeasurePreserving (h * ·) ν ν) → ∀ E : Set N, IsFundamentalDomain (R.subgroupOf N) E νN → IsFundamentalDomain (R.subgroupOf (Q ⊔ N)) (Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) '' E) ν := by
  first | exact @GlobalTheory.FdTransfer.isFundamentalDomain_inclusion_image | exact GlobalTheory.FdTransfer.isFundamentalDomain_inclusion_image | (intros; apply GlobalTheory.FdTransfer.isFundamentalDomain_inclusion_image <;> assumption)
