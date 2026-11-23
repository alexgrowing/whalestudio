import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberBadPrimesNoConjugatePair
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberBadPrimes_no_conjugatePair : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  first | exact @GlobalTheory.BadNoConj.sall_noConj_ok | exact GlobalTheory.BadNoConj.sall_noConj_ok | (intros; apply GlobalTheory.BadNoConj.sall_noConj_ok <;> assumption)
