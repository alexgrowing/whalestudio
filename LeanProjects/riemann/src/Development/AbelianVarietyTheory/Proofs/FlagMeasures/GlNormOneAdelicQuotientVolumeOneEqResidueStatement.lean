import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glNormOneAdelicQuotientVolume_one_eq_residue : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → glVol E 1 = ENNReal.ofReal (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
  first | exact @GlobalTheory.NormOneVol.glVol_one | exact GlobalTheory.NormOneVol.glVol_one | (intros; apply GlobalTheory.NormOneVol.glVol_one <;> assumption)
