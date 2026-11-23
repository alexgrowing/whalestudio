import Mathlib
import Formalism.LocalToGlobal.ExponentGrids.SecondComplementClosedValuation
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PBrDiv

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.CG (HCdeg HCDplus HCDminus)
open Formalism.D5 (PhiSet E0)
open Formalism.LFunctionChainParameters.characterSumData (ArithData)
open Formalism.RankGapBounds.WeightedMeanData (Consts)
open Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6
open Formalism.LFunctionChainParameters.LBrDiv (plOf TypePrimeCostDeviationBound)

noncomputable section

namespace Formalism.AtG

namespace PlacesLyingOver

open Formalism.DivisionValues.PlaceSumConjugation

variable {K : Type} [Field K] [NumberField K]

theorem vw_mul' (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul K w
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 ha)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hb)

theorem vw_one' (w : HeightOneSpectrum (𝓞 K)) : vw w (1 : K) = 0 := by
  unfold vw
  rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem vw_pow' (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0) (n : ℕ) :
    vw w (a ^ n) = (n : ℤ) * vw w a := by
  induction n with
  | zero => simp [vw_one']
  | succ n ih =>
    rw [pow_succ, vw_mul' w _ _ (pow_ne_zero n ha) ha, ih]
    push_cast
    ring

end PlacesLyingOver

open PlacesLyingOver Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation

end Formalism.AtG
