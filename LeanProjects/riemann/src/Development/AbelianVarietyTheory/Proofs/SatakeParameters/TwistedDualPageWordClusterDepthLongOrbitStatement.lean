import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbit
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf φ.2 → (pageWord L j ε τ φ).HypA (depth L l) := by
  first | exact @GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | exact GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit | (intros; apply GlobalTheory.HTW.pageWord_hypA_depth_of_long_orbit <;> assumption)
