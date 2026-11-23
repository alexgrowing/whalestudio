import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (N : Submodule R' A'), N.FG → ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  first | exact @GlobalTheory.fg_localizationAway_span_finset | exact GlobalTheory.fg_localizationAway_span_finset | (intros; apply GlobalTheory.fg_localizationAway_span_finset <;> assumption)
