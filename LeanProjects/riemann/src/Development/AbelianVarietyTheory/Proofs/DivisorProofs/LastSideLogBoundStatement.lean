import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_side_log_bound : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound → ∀ (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), WeightTie N W pl u δ → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T u) → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R 25 (lastLog W u) := by
  first | exact @GlobalTheory.ColRows.LastSideProof.lastSide | exact GlobalTheory.ColRows.LastSideProof.lastSide | (intros; apply GlobalTheory.ColRows.LastSideProof.lastSide <;> assumption)
