import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopMulDescendedSubmoduleOfUnitCocycleEqTop
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_mul_descendedSubmoduleOfUnitCocycle_eq_top : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : (B ⊗[A] B)ˣ), UCoc A B u → (⊤ : Submodule A B) * descMod A B u = ⊤ := by
  first | exact @GlobalTheory.DescTop.top_mul_descMod_eq_top | exact GlobalTheory.DescTop.top_mul_descMod_eq_top | (intros; apply GlobalTheory.DescTop.top_mul_descMod_eq_top; all_goals assumption)
