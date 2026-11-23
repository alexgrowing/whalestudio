import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedCountGluedLatticesEqMassMulLocal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_count_glued_lattices_eq_mass_mul_local : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → TotPos (Gval F F') → ∀ (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → MassLaw F F' P d0 V → ∀ s : Finset (LV D), Glue G G' s → ENNReal.ofReal (glueSum G G' s) = ENNReal.ofReal V * ∏ p ∈ P, locSum G G' p (R p) (d0 p) := by
  first | exact @GlobalTheory.GlueCount.glue_count | exact GlobalTheory.GlueCount.glue_count | (intros; apply GlobalTheory.GlueCount.glue_count <;> assumption)
