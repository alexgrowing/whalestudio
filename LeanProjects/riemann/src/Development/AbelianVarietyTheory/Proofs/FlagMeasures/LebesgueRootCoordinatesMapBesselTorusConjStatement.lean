import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueRootCoordinatesMapBesselTorusConj
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lebesgue_rootCoordinates_map_besselTorus_conj : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 → (D.muN k r).map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • D.muN k r := by
  first | exact @GlobalTheory.ThA.TorusJac.muN_map_conj | exact GlobalTheory.ThA.TorusJac.muN_map_conj | (intros; apply GlobalTheory.ThA.TorusJac.muN_map_conj <;> assumption)
