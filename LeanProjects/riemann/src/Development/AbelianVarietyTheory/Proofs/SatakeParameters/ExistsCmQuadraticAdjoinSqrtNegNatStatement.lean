import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmQuadraticAdjoinSqrtNegNat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmQuadratic_adjoin_sqrt_neg_nat : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) → ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  first | exact @GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg | exact GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg | (intros; apply GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg <;> assumption)
