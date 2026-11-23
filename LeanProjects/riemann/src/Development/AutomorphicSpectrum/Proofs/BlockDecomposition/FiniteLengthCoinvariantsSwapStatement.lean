import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthCoinvariantsSwap
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_coinvariants_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ), HasFiniteLength (coinv (omega b a μ⁻¹) (detChar b χ⁻¹)) → HasFiniteLength (coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.Swap.coinv_swap_finiteLength | exact GlobalTheory.CompanionTheory.ThetaGLLen.Swap.coinv_swap_finiteLength | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.Swap.coinv_swap_finiteLength <;> assumption)
