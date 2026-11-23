import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.XLamLeSmulSupXLamAdmissibleFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xLam_le_smul_sup_xLam_admissible_flag : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), IsFixedConv Λ g F → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  first | exact @GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam | exact GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam | (intros; apply GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam <;> assumption)
