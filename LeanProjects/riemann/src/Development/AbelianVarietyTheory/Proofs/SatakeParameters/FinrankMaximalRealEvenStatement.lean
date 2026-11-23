import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankMaximalRealEven
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_maximal_real_even : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] (Q : GlobalTheory.RealGal.QCM E Ω), Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  first | exact @GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield | exact GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield | (intros; apply GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield <;> assumption)
