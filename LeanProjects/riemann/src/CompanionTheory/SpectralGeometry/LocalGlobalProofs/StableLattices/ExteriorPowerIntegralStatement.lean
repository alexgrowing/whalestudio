import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExteriorPowerIntegral : OKWedge := by
  first | exact @GlobalTheory.CompanionTheory.ZuckWedge.okWedge | exact GlobalTheory.CompanionTheory.ZuckWedge.okWedge | (intros; apply GlobalTheory.CompanionTheory.ZuckWedge.okWedge <;> assumption)
