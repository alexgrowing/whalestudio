import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedFrameOfIsotropicColumns

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' : ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))), Module.finrank E Y = r → ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E), Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y → ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose → (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) → ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E) (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E), C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧ J * L + K * M = 1 := by
  first | exact @GlobalTheory.exists_adapted_frame_of_isotropic_columns | exact GlobalTheory.exists_adapted_frame_of_isotropic_columns | (intros; apply GlobalTheory.exists_adapted_frame_of_isotropic_columns <;> assumption)
