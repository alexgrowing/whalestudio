import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  first | exact @GlobalTheory.CellLieAlg.lie_entries | exact GlobalTheory.CellLieAlg.lie_entries | (intros; apply GlobalTheory.CellLieAlg.lie_entries <;> assumption)
