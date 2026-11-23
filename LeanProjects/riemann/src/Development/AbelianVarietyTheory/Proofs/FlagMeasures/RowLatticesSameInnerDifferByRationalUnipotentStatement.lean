import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameInnerDifferByRationalUnipotent
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent : ∀ (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λa Λb : LV D) (σ : GV D), IsRowLat D F0 Λa → IsRowLat D F0 Λb → Adapt σ (lf D F0) (lf D F0) → Lsub (Formalism.HermitianLatticesTheory.gmap σ Λa) (lf D F0) = Lsub Λb (lf D F0) → ∃ n ∈ NRat (lf D F0), Formalism.HermitianLatticesTheory.gmap (n * σ) Λa = Λb := by
  first | exact @GlobalTheory.Unfold.sameInner_unip | exact GlobalTheory.Unfold.sameInner_unip | (intros; apply GlobalTheory.Unfold.sameInner_unip <;> assumption)
