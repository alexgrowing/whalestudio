import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbedding
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.floor_size_bounds_not_thick_embedding : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  first | exact @GlobalTheory.HTW.size_not_thick | exact GlobalTheory.HTW.size_not_thick | (intros; apply GlobalTheory.HTW.size_not_thick <;> assumption)
