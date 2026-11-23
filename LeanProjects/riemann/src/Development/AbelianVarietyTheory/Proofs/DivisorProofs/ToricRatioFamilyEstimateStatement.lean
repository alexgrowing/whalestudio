import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFamilyEstimate
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_family_estimate : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx → (Lf (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  first | exact @GlobalTheory.ThmAUpper.thmA_upper | exact GlobalTheory.ThmAUpper.thmA_upper | (intros; apply GlobalTheory.ThmAUpper.thmA_upper <;> assumption)
