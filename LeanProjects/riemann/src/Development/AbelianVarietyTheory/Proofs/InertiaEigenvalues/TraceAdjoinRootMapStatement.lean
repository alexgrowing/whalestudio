import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceAdjoinRootMap
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_trace_adjoinRoot_eq_trace_map : ∀ (R S : Type) [CommRing R] [CommRing S] (g : R →+* S) (h : R[X]), h.Monic → ∀ x : AdjoinRoot h, g (Algebra.trace R (AdjoinRoot h) x) = Algebra.trace S (AdjoinRoot (h.map g)) (AdjoinRoot.map g h (h.map g) dvd_rfl x) := by
  first | exact @GlobalTheory.trace_adjoinRoot_map | exact GlobalTheory.trace_adjoinRoot_map | (intros; apply GlobalTheory.trace_adjoinRoot_map <;> assumption)
