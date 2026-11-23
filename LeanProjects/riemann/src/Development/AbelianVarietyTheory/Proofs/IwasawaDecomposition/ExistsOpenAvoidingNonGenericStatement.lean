import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenAvoidingNonGeneric
import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_avoiding_non_generic : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : X → Prop) (G : Set X), IsOpen G → ∀ (U : X.Opens) (z : X), z ∈ U → (∀ q ∈ U, P q → ∀ η : X, η ⤳ q → η ≠ q → η ∈ G) → ∃ V : X.Opens, V ≤ U ∧ z ∈ V ∧ ∀ q ∈ V, P q → q ∈ G ∨ q ⤳ z := by
  first | exact @GlobalTheory.shrink_nbhd_generise_centre | exact GlobalTheory.shrink_nbhd_generise_centre | (intros; apply GlobalTheory.shrink_nbhd_generise_centre <;> assumption)
