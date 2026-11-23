import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.node_function_levi_decomposition : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply | exact GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply <;> assumption)
