import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFittedIdentity
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrality_fitted_identity : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → BotSmall → BotNe → GlobalTheory.BigTop.Fun.Int @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.int_tie | exact GlobalTheory.BigTop.Fun.int_tie | (intros; apply GlobalTheory.BigTop.Fun.int_tie <;> assumption)
