import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterization
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEntries_unipotentBesselN_characterization : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (Nset k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → unrealify x i j = 0)) ∧ (x ∈ lieE (Nset k r) → NormedSpace.exp (unrealify x) ∈ Nset k r) := by
  first | exact @GlobalTheory.CellDens.LieN.lieE_Nset | exact GlobalTheory.CellDens.LieN.lieE_Nset | (intros; apply GlobalTheory.CellDens.LieN.lieE_Nset <;> assumption)
