import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPoint
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ), M.MChart ω → M.At ω ζ p → hat M.ι (C ω * logS) (fun z => M.u (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.u) ∧ hat M.ι (C ω * logS) (fun z => M.w (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.w) := by
  first | exact @GlobalTheory.MomOne.SmallTranslate.shift_eq_translate | exact GlobalTheory.MomOne.SmallTranslate.shift_eq_translate | (intros; apply GlobalTheory.MomOne.SmallTranslate.shift_eq_translate <;> assumption)
