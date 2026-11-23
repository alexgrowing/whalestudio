import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroOfHoweUnramified
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_nonzero_of_howe_unramified : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.NRows.HypothesesX → ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  first | exact @GlobalTheory.DownLift.AtReal.main | exact GlobalTheory.DownLift.AtReal.main | (intros; apply GlobalTheory.DownLift.AtReal.main <;> assumption)
