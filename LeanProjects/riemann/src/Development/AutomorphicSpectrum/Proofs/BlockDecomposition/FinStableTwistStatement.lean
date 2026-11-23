import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finStable_twist : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z : ℂ), FinStable U → FinStable (tw U z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.finStable_tw | exact GlobalTheory.CompanionTheory.LimV.finStable_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.finStable_tw <;> assumption)
