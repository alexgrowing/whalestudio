import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningImageLattice
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spanning_image_lattice : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h : ℕ) (π : (Fin h → C) →ₗ[C] V), Function.Surjective π → ∃ g : Fin h → V, Submodule.span C (Set.range g) = ⊤ ∧ Set.range (fun t : Fin h → O => π (fun i => algebraMap O C (t i))) = (Submodule.span O (Set.range g) : Set V) := by
  first | exact @GlobalTheory.image_integral_points_eq_span_of_surjective | exact GlobalTheory.image_integral_points_eq_span_of_surjective | (intros; apply GlobalTheory.image_integral_points_eq_span_of_surjective <;> assumption)
