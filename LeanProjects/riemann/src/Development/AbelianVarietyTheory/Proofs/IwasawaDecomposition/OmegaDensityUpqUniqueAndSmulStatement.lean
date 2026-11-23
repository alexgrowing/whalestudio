import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omegaDensity_upq_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal), OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧ ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  first | exact @GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul | exact GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul | (intros; apply GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul <;> assumption)
