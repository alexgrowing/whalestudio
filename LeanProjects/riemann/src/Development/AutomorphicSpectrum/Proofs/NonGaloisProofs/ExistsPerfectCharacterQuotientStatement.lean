import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotient
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perfect_character_quotient : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (r N : ℕ), 0 < N → Finite (O ⧸ Ideal.span {ϖ ^ r}) → ((N : O) ∈ Ideal.span {ϖ ^ r}) → ∃ ψ₀ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, (∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) ∧ ∀ ψ : (O ⧸ Ideal.span {ϖ ^ r}) →+ ZMod N, ∃ o, ∀ x, ψ x = ψ₀ (o * x) := by
  first | exact @GlobalTheory.CompanionTheory.LocDual.GenChar.exists_generating_character | exact GlobalTheory.CompanionTheory.LocDual.GenChar.exists_generating_character | (intros; apply GlobalTheory.CompanionTheory.LocDual.GenChar.exists_generating_character <;> assumption)
