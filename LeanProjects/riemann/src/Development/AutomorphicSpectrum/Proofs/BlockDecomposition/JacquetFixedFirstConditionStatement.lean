import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedFirstCondition
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_fixed_first_condition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | exact GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | (intros; apply GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul <;> assumption)
