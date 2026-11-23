import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportProductOverPlaces
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_product_over_places : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (N : Set (Q d β (AF F))), (1 : Q d β (AF F)) ∈ N →
  (∀ x ∈ N, ∀ y ∈ N, x * y ∈ N) → (∀ u : Pl F, SuppAt d β {u} ⊆ N) →
  ∀ T : Finset (Pl F), SuppAt d β (T : Set (Pl F)) ⊆ N := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places | exact GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.ProdSupp.suppAt_subset_of_places <;> assumption)
