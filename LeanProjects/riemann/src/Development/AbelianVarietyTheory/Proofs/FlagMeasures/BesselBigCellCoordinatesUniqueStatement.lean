import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselBigCellCoordinatesUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselBigCell_coordinates_unique : ∀ (k r : ℕ) (x y : Fin r → ℂ), (∀ a, x a ≠ 0) → (∀ a, y a ≠ 0) → ∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, ∀ n₁' ∈ Nset k r, ∀ n₂' ∈ Nset k r, ∀ m₁ ∈ Formalism.FourierDecayAlt.B2.UWb k r, ∀ m₂ ∈ Formalism.FourierDecayAlt.B2.UWb k r, n₁⁻¹ * bigCell k r x 1 * m₁ * n₁' = n₂⁻¹ * bigCell k r y 1 * m₂ * n₂' → n₁ = n₂ ∧ x = y ∧ m₁ = m₂ ∧ n₁' = n₂' := by
  first | exact @GlobalTheory.CellDens.bigCell_coords_unique | exact GlobalTheory.CellDens.bigCell_coords_unique | (intros; apply GlobalTheory.CellDens.bigCell_coords_unique <;> assumption)
