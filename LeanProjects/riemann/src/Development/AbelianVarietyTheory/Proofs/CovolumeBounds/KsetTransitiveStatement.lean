import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.KsetTransitive
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq : ∀ k r : ℕ, 1 ≤ k → ∀ g ∈ GV k r, ∃ κ ∈ Kset k r, ∃ p ∈ Pset k r, g = κ * p := by
  first | exact @GlobalTheory.HCXi.iwasawa | exact GlobalTheory.HCXi.iwasawa | (intros; apply GlobalTheory.HCXi.iwasawa <;> assumption)
