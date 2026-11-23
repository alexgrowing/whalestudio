import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingCharacterPhaseOriginValuationLeBox
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box : ∀ {k : Type} [Field k] [ValuativeRel k] (G : Grid k) (ϖ : kˣ) (a a' : ℤ) (e : Vars G), e ∈ box G ϖ a a' → valuation k (phase (0 : ColArgs G) e) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
  first | exact @GlobalTheory.OriginBox.phase_origin_le | exact GlobalTheory.OriginBox.phase_origin_le | (intros; apply GlobalTheory.OriginBox.phase_origin_le <;> assumption)
