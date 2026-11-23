import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCosetRepsUnipotent
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_coset_reps_unipotent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ D.J ⊓ D.N) ∧ ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom | exact GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom | (intros; apply GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom <;> assumption)
