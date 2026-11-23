import Mathlib
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.TailInequalityEventually
import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional
import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates
import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkageAlt

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem sum_exponent_log_le_of_cut :
    Formalism.CohomologicalDescent.E.ExCut → ∀ (P : Par) (X' A : ℝ), P.Hyp → P.Large → LargeParameterEstimates.Rows P X' A → LargeParameterEstimates.Big P.L P.x X' A →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f → W.Sp.card ≤ 5 →
    ∀ T : ℕ, W.T2.card ≤ T → ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
    ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b := by
  intro hC P X' A hH hL hR hB ι _ _ W hW hcard hSp T hT Q hQ
  have hs := Formalism.CohomologicalDescent.E.recursion_sum_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC Formalism.CohomologicalDescent.Top.prime_count_bound_rs
    P hH hL ι W hW hcard hSp Q hQ
  have hTf : W.T2.card ≤ P.f := by rw [← hcard]; exact Finset.card_le_univ _
  have ht := LargeParameterEstimates.tail_bound_holds P X' A _ hH hR hB hTf
  have F := LargeParameterEstimates.large_parameter_facts_of_hyp hH hR hB
  have hb : 0 ≤ P.b := F.b_pos.le
  have hm : (0 : ℝ) ≤ (P.m : ℝ) * P.b * P.L ^ 2 := by positivity
  have hTT : (W.T2.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have key : 30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 ≤ 30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 := by
    nlinarith
  linarith

end GlobalTheory
