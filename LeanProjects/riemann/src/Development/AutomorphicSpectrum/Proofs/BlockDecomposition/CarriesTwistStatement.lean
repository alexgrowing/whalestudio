import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_twist : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) (z : ℂ), Carries e U U' → Carries e (tw U z) (tw U' z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.carries_tw | exact GlobalTheory.CompanionTheory.LimV.carries_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.carries_tw <;> assumption)
