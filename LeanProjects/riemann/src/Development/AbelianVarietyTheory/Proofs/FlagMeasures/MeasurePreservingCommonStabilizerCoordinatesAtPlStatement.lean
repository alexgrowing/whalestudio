import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCommonStabilizerCoordinatesAtPl
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_commonStabilizerCoordinatesAtPlace : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  first | exact @GlobalTheory.DegVol.RefCov.atP_measurePreserving | exact GlobalTheory.DegVol.RefCov.atP_measurePreserving | (intros; apply GlobalTheory.DegVol.RefCov.atP_measurePreserving <;> assumption)
