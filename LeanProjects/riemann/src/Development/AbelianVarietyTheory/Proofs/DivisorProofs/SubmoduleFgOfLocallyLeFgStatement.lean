import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem : ∀ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R] (M : Submodule R A) (s : Set R), Ideal.span s = ⊤ → (∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) → M.FG := by
  first | exact @GlobalTheory.submodule_fg_of_locally_le_fg | exact GlobalTheory.submodule_fg_of_locally_le_fg | (intros; apply GlobalTheory.submodule_fg_of_locally_le_fg <;> assumption)
