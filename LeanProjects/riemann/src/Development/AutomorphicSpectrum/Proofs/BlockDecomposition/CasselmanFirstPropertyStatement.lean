import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstProperty
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casselman_first_property : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A1 G := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | exact GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | (intros; apply GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract <;> assumption)
