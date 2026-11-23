import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenLeClosedFibre
import Mathlib
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_open_le_closed_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le | exact GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le <;> assumption)
