import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAdelicQuotientVolumePosLtTop
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_quotient_volume_pos_lt_top : VolumeStep → ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ p q : ℕ, HasSig I p q → 2 ≤ p → 0 < I.muA μf fund ∧ I.muA μf fund < ⊤ := by
  first | exact @GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top | exact GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top | (intros; apply GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top <;> assumption)
