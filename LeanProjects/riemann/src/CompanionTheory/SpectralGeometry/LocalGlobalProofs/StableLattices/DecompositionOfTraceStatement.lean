import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DecompositionOfTrace : DecOfTrace := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | exact GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | (intros; apply GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace <;> assumption)
