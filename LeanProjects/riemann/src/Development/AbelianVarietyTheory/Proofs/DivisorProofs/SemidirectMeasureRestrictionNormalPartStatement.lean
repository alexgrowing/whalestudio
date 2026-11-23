import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectMeasureRestrictionNormalPart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_measure_restriction_normal_part : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G), IsClosed (N : Set G) → (∀ h ∈ Q ⊔ N, ∃ n ∈ N, ∃ q ∈ Q, n * q = h) → ∀ [Countable Q] (νN : Measure N), (∀ n : N, MeasurePreserving (· * n) νN νN) → ∀ A : Set N, supMeas N Q νN (Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) '' A) = νN A := by
  first | exact @GlobalTheory.supMeas_image_inclusion | exact GlobalTheory.supMeas_image_inclusion | (intros; apply GlobalTheory.supMeas_image_inclusion <;> assumption)
