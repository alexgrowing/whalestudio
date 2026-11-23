import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermTranslateByAdaptedLatticeAutomorphisms
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_term_translate_by_adapted_lattice_automorphisms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'), ∀ a ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∃ s : TauC Y u u', s.lam = t.lam ∧ s.lam' = t.lam' ∧ ∃ n ∈ NLam t.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t.lam' (lf D (X.Fu u')), s.lin = n * (a * t.lin * a'⁻¹) * n' := by
  first | exact @GlobalTheory.TransT.trans_main | exact GlobalTheory.TransT.trans_main | (intros; apply GlobalTheory.TransT.trans_main <;> assumption)
