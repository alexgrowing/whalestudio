import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryFixingSpanPreservesGluedLattices
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometryFixingSpan_preserves_gluedLattices : ∀ (D : D7) (U : Submodule D.host.E (VS D).V) (M : Submodule (𝓞 D.host.E) (VS D).V), ∀ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U, ∀ Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M, Formalism.HermitianLatticesTheory.gmap g Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M := by
  first | exact @GlobalTheory.GlueStable.glueSet_gmap_mem | exact GlobalTheory.GlueStable.glueSet_gmap_mem | (intros; apply GlobalTheory.GlueStable.glueSet_gmap_mem <;> assumption)
