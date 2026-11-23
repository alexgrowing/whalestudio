import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableInducedSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finStable_induced_span : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), FinStable (indSpan U₁ U₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.indSpan_finStable | exact GlobalTheory.CompanionTheory.LimV.indSpan_finStable | (intros; apply GlobalTheory.CompanionTheory.LimV.indSpan_finStable <;> assumption)
