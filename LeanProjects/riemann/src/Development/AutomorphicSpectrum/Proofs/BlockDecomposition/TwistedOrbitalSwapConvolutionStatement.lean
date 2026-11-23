import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolution
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PLocPrjGOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiagonalDoubleCosetsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistedCentralizerDiagonalStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_swap_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ),
  IsOpen (K : Set H) → IsCompact (K : Set H) → IsOpen (L : Set H) → L ≤ K → IsHecke L f₁ → IsHecke L f₂ → Good (MonoidHom.id H) K N →
  (∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d) →
  twOrb ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (N, 1) (fun y => f₁ y.1 * f₂ y.2) =
    twOrb (MonoidHom.id H) K N (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitSwap.main | exact GlobalTheory.CompanionTheory.SplitSwap.main | (intros; apply GlobalTheory.CompanionTheory.SplitSwap.main <;> assumption)
