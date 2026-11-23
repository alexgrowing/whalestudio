import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent : ∀ (D : D7) {T : D.host.E} (F : LFlag (VS D) D.R.rS T), T ≠ 0 → (∀ A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Uni A → ∃ F₁ : LFlag (VS D) D.R.rS T, Chg (frame F) A (frame F₁)) ∧ (∀ F₁ : LFlag (VS D) D.R.rS T, Tri D.host.E (frame F) (frame F₁) ↔ ∃ n ∈ Formalism.L2.SG.NGData.NRat F, ∀ a, frame F₁ a = n (frame F a)) := by
  first | exact @GlobalTheory.FlagChange.flag_change | exact GlobalTheory.FlagChange.flag_change | (intros; apply GlobalTheory.FlagChange.flag_change <;> assumption)
