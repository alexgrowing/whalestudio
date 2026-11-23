import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericTermClassesEqRowsInDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGeneric_term_classes_eq_rows_in_double_coset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → ClsRow (Y.tO u u').ngSet (clsOf Y u u') := by
  first | exact @GlobalTheory.Unfold.RowCls.clsRow_ngSet | exact GlobalTheory.Unfold.RowCls.clsRow_ngSet | (intros; apply GlobalTheory.Unfold.RowCls.clsRow_ngSet <;> assumption)
