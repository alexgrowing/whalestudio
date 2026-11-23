import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategory
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HomCategory : HomCat := by
  first | exact @GlobalTheory.CompanionTheory.ZuckHomCat.homCat | exact GlobalTheory.CompanionTheory.ZuckHomCat.homCat | (intros; apply GlobalTheory.CompanionTheory.ZuckHomCat.homCat <;> assumption)
