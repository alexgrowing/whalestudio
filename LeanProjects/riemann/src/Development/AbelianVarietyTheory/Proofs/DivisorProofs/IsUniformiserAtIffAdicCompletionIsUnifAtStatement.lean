import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUniformiserAtIffAdicCompletionIsUnifAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt : ∀ {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ), IsUniformiserAt K v (x : v.adicCompletion K) ↔ Formalism.L2.Host.IsUnifAt v x := by
  first | exact @GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt | exact GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt | (intros; apply GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt <;> assumption)
