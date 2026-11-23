import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicGeneratorsSeparableMin
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction
open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclic_generators_separable_min : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (G : Type) [AddCommGroup G] [Module κ G]
    [FiniteDimensional κ G] (T : Module.End κ G) (h : κ[X]) (_ : h.Monic) (_ : h.Separable)
    (_ : aeval T h = 0) (N : ℕ) (_ : LinearMap.charpoly T = h ^ N),
    ∃ x : Fin N → G, ∀ v : G, ∃ p : Fin N → κ[X], v = ∑ j, aeval T (p j) (x j) := by
  first | exact @GlobalTheory.semisimple_charpoly_pow_generators | exact GlobalTheory.semisimple_charpoly_pow_generators | (intros; apply GlobalTheory.semisimple_charpoly_pow_generators <;> assumption)
