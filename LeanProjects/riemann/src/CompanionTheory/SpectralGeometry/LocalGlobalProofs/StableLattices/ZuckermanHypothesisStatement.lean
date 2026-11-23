import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesis
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.BetaAtInfinityZero
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zuckerman_hypothesis : ZuckH := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds | exact GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds | (intros; apply GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds <;> assumption)
