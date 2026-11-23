import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeConditionHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_condition_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  first | exact @GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp | exact GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp | (intros; apply GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp <;> assumption)
