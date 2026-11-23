import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectivePiAdjoinRootKerEqRange
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_pi_adjoinRoot_ker_eq_range' : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) [Fact (Irreducible f)], ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧ (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧ LinearMap.ker π = LinearMap.range (aeval g f) ∧ Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by
  first | exact @GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range | exact GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range | (intros; apply GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range <;> assumption)
