import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowers_ext_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B), ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_isStd | exact GlobalTheory.PDA.PDPoly.exists_isStd | (intros; apply GlobalTheory.PDA.PDPoly.exists_isStd <;> assumption)
