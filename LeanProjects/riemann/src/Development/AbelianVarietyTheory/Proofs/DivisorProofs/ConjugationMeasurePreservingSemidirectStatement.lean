import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationMeasurePreservingSemidirect
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_measure_preserving_semidirect : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G), (∀ h ∈ Q ⊔ N, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → ∀ (νN : Measure N), (∀ n : N, MeasurePreserving (· * n) νN νN) → MeasurePreserving (fun n : N => n⁻¹) νN νN → (∀ h ∈ Q ⊔ N, ∀ f : N → N, (∀ n, (f n : G) = h * n * h⁻¹) → MeasurePreserving f νN νN) → MeasurePreserving (fun p : ↥(Q ⊔ N) => p⁻¹) (supMeas N Q νN) (supMeas N Q νN) := by
  first | exact @GlobalTheory.SupMeasInv.supMeas_inv_invariant | exact GlobalTheory.SupMeasInv.supMeas_inv_invariant | (intros; apply GlobalTheory.SupMeasInv.supMeas_inv_invariant <;> assumption)
