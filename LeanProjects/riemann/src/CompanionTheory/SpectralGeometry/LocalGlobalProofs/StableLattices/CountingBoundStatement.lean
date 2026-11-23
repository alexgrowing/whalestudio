import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBound
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CountingBound : Count := by
  first | exact @GlobalTheory.CompanionTheory.ZuckCount.count | exact GlobalTheory.CompanionTheory.ZuckCount.count | (intros; apply GlobalTheory.CompanionTheory.ZuckCount.count <;> assumption)
