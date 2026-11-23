import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarCorankOnePairsTrans
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarCorankOnePairs_trans : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' t'' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → t''.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'' := by
  first | exact @GlobalTheory.ScalTrans.scalar_pair_trans | exact GlobalTheory.ScalTrans.scalar_pair_trans | (intros; apply GlobalTheory.ScalTrans.scalar_pair_trans <;> assumption)
