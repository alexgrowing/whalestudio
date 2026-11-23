import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_levi_radical_coords_homeomorph : ∀ k r : ℕ, Set.BijOn (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) Set.univ (Nset k r) ∧ Continuous (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) ∧ ∃ c : Mat k r → (UT r → ℂ) × PPar k r, Continuous c ∧ ∀ q : (UT r → ℂ) × PPar k r, c (uEmb k r (upper q.1) * pOf k r q.2) = q := by
  first | exact @GlobalTheory.Amp.NCoord.coord_homeo | exact GlobalTheory.Amp.NCoord.coord_homeo | (intros; apply GlobalTheory.Amp.NCoord.coord_homeo <;> assumption)
