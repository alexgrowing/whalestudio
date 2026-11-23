import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometricEmbeddedDatumPairsEncardIsometrySmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometricEmbeddedDatumPairs_encard_isometry_smul : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) W), (Trip HW g (s • L) j x x').encard = (Trip HW g L j x x').encard := by
  first | exact @GlobalTheory.TripInv.trip_encard_smul | exact GlobalTheory.TripInv.trip_encard_smul | (intros; apply GlobalTheory.TripInv.trip_encard_smul <;> assumption)
