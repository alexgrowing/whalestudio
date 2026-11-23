import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardExactGramIntegralFrameClassesLe
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_exactGramIntegralFrameClasses_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  first | exact @GlobalTheory.LoopC.FrEx.cntCl_ExSet_le | exact GlobalTheory.LoopC.FrEx.cntCl_ExSet_le | (intros; apply GlobalTheory.LoopC.FrEx.cntCl_ExSet_le <;> assumption)
