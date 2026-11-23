import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorLiftDominant
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_vector_lift_dominant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ w ∈ fixed (D.piN π) D.JT, ∃ j : ℕ, ∃ v : fixed π D.J, D.proj π (v : V) = D.piN π (t ^ j) w := by
  first | exact @GlobalTheory.CompanionTheory.CassPush.exists_fixed_proj_eq_piN_pow | exact GlobalTheory.CompanionTheory.CassPush.exists_fixed_proj_eq_piN_pow | (intros; apply GlobalTheory.CompanionTheory.CassPush.exists_fixed_proj_eq_piN_pow <;> assumption)
