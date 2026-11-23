import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_prodSpan : ∀ {A B : Type} (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)), FiniteDimensional ℂ U₁ → FiniteDimensional ℂ U₂ → FiniteDimensional ℂ (prodSpan U₁ U₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd | exact GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd | (intros; apply GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd <;> assumption)
