import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfield
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedAdjoinSqrtOfNotMem
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_unramified_over_maximalRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal := by
  first | exact @GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield | exact GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield | (intros; apply GlobalTheory.exists_nat_unramified_over_real_of_cm_subfield <;> assumption)
