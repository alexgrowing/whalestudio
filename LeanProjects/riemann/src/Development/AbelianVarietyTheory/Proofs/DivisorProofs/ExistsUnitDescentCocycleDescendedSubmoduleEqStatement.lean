import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDescentCocycleDescendedSubmoduleEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitDescentCocycle_descendedSubmodule_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], descMod A B 1 ≤ 1 → ∀ I : (Submodule A B)ˣ, ∃ u : (B ⊗[A] B)ˣ, UCoc A B u ∧ descMod A B u = (I : Submodule A B) := by
  first | exact @GlobalTheory.PicCech.exists_unitCocycle_descMod_eq | exact GlobalTheory.PicCech.exists_unitCocycle_descMod_eq | (intros; apply GlobalTheory.PicCech.exists_unitCocycle_descMod_eq; all_goals assumption)
