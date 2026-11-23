import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepSequenceShortExact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.FlagChi Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_sequence_short_exact : ∀ (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ) (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z) (r : L.ι → Z.functionFieldˣ) (hr : IsRatSec L r), L.IsLB → Epi (stepProj M l hr) → (stepSeq M l hr).ShortExact := by
  first | exact @GlobalTheory.FlagChi.stepSeq_shortExact | exact GlobalTheory.FlagChi.stepSeq_shortExact | (intros; apply GlobalTheory.FlagChi.stepSeq_shortExact <;> assumption)
