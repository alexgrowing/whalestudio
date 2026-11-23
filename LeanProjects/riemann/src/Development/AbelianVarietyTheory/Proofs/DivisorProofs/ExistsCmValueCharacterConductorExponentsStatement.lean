import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmValueCharacterConductorExponents
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmValueCharacter_conductorExponents : ∀ (D : D7) [IsCMField D.host.E] {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (s : ℕ)
    (κ : D.what₂.Tau → ℕ) (χ : HChar D.host.E), IsValChar (cmPhi D) s κ (condF G.pl) ∅ χ →
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) →₀ ℕ, (∀ v, ExpAt χ v (a v)) ∧
      (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) ≤ levQ G.pl ^ 2 := by
  first | exact @GlobalTheory.FunObj.SqNum.CondExps.exists_condExps | exact GlobalTheory.FunObj.SqNum.CondExps.exists_condExps | (intros; apply GlobalTheory.FunObj.SqNum.CondExps.exists_condExps <;> assumption)
