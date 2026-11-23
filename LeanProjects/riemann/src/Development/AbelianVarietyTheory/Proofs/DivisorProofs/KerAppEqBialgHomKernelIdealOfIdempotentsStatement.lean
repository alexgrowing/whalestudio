import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotents
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_app_eq_bialgHomKernelIdeal_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, RingHom.ker (u.app n) = kerIdeal (v.app n) := by
  first | exact @GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents | exact GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents | (intros; apply GlobalTheory.PDivGroup.ker_app_eq_kerIdeal_of_idempotents <;> assumption)
