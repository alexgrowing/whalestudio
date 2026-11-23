import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_node_function : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn | exact GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeFlat.flatFn_nodeFn <;> assumption)
