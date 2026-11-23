import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletions
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_unimodular_lattice_iff_local_completions : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) → ∀ Λ : LV D, Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ Submodule.IsLattice D.host.E Λ ∧ ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) ∧ (∀ i, (locH Z p).MMfam (tm FP G G' p (lattice₂ D Z.M p Λ)) i ∈ lattice₂ D Z.M p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p (lattice₂ D Z.M p Λ)) := by
  first | exact @GlobalTheory.GenMass.GlueLoc.glue_iff_local | exact GlobalTheory.GenMass.GlueLoc.glue_iff_local | (intros; apply GlobalTheory.GenMass.GlueLoc.glue_iff_local <;> assumption)
