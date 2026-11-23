import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNode
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunctionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_induced_node : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (U₁ U₁' : Submodule ℂ (Sm E r)) (U₂ U₂' : Submodule ℂ (Sm E s)), FlatFn e₁ → FlatFn e₂ → FinStable U₁ → FinStable U₁' → FinStable U₂ → FinStable U₂' → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → Carries (nodeFn e₁ e₂) (indSpan U₁ U₂) (indSpan U₁' U₂') := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn | exact GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn <;> assumption)
