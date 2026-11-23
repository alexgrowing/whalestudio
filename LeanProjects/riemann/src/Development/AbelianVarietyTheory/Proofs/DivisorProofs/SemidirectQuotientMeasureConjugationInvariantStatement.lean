import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectQuotientMeasureConjugationInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_quotient_measure_conjugation_invariant : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G), (∀ h ∈ Q ⊔ N, ∃ n ∈ N, ∃ q ∈ Q, n * q = h) → ∀ [Countable Q], (∀ h ∈ Q ⊔ N, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → ∀ (νN : Measure N) [SFinite νN], (∀ n : N, MeasurePreserving (· * n) νN νN) → (∀ h ∈ Q ⊔ N, ∀ f : N → N, (∀ n, (f n : G) = h * n * h⁻¹) → MeasurePreserving f νN νN) → SFinite (supMeas N Q νN) ∧ ∀ h : ↥(Q ⊔ N), MeasurePreserving (h * ·) (supMeas N Q νN) (supMeas N Q νN) := by
  first | exact @GlobalTheory.SupMeas.supMeas_sfinite_invariant | exact GlobalTheory.SupMeas.supMeas_sfinite_invariant | (intros; apply GlobalTheory.SupMeas.supMeas_sfinite_invariant <;> assumption)
