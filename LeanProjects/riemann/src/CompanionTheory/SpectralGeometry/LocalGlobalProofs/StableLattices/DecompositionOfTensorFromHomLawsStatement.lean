import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLaws
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_of_tensor_from_hom_laws : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecTens.decTens | exact GlobalTheory.CompanionTheory.ZuckDecTens.decTens | (intros; apply GlobalTheory.CompanionTheory.ZuckDecTens.decTens <;> assumption)
