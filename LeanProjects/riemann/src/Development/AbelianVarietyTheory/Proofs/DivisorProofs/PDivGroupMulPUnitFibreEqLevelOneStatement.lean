import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupMulPUnitFibreEqLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k] [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : GlobalTheory.PDivGroup p R) (n : ℕ), Function.Surjective (fun a : G.A (n + 1) => ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧ ∀ a : G.A (n + 1), ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔ a ∈ (RingHom.ker ((algebraMap R k).comp (Bialgebra.counitAlgHom R (G.A n) : G.A n →+* R))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  first | exact @GlobalTheory.fibre_statement | exact GlobalTheory.fibre_statement | (intros; apply GlobalTheory.fibre_statement <;> assumption)
