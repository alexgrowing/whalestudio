import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedIdeleEqLocalIdele
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedIdele_eq_localIdele : ∀ {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {a : Ideles K}, IsSupportedAt K a v → ∃ x : (v.adicCompletion K)ˣ, (x : v.adicCompletion K) = (a : AdeleRing (𝓞 K) K).2 v ∧ localIdele K v x = a := by
  first | exact @GlobalTheory.Div.SuppIdele.supported_eq_localIdele | exact GlobalTheory.Div.SuppIdele.supported_eq_localIdele | (intros; apply GlobalTheory.Div.SuppIdele.supported_eq_localIdele <;> assumption)
