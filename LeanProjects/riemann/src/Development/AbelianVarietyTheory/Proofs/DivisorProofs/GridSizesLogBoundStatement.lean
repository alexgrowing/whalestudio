import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSizesLogBound
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
open NumberField GlobalTheory.SqTop GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridSizes_log_bound : ∀ c : ℝ, GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    c * (Module.finrank ℚ D.host.E : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((kap D sc.cGap i j s τ : ℝ) + s)) ≤ bTH D C x b := by
  first | exact @GlobalTheory.SqTop.SizesBound.sizes | exact GlobalTheory.SqTop.SizesBound.sizes | (intros; apply GlobalTheory.SqTop.SizesBound.sizes <;> assumption)
