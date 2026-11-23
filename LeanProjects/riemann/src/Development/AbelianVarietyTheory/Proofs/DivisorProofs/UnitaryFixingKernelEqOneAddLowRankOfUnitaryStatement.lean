import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingKernelEqOneAddLowRankOfUnitary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fixing_kernel_eq_oneAddLowRank_of_unitary : ∀ (R : Type) [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) R), IsUnit J.det → ∀ (A : Matrix (Fin M) (Fin 2) R) (B : Matrix (Fin 2) (Fin M) R) (H : Matrix (Fin 2) (Fin 2) R), B * A = 1 → Formalism.UG.cT c A * J = H * B → J * A = Formalism.UG.cT c B * H → ∀ G : Matrix (Fin M) (Fin M) R, Formalism.UG.cT c G * J * G = J → G * (1 - A * B) = 1 - A * B → G = emb A B (B * G * A) ∧ Formalism.UG.cT c (B * G * A) * H * (B * G * A) = H := by
  first | exact @GlobalTheory.PlaneSU.eq_emb_of_fix | exact GlobalTheory.PlaneSU.eq_emb_of_fix | (intros; apply GlobalTheory.PlaneSU.eq_emb_of_fix <;> assumption)
