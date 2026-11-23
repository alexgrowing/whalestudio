import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeCompatHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_compat_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat | exact GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat | (intros; apply GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat <;> assumption)
