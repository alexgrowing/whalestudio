import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue
import Mathlib
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntegers_henselian_finiteResidue : ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧ Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  first | (exact @GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (exact GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (intros; apply GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField <;> assumption)
