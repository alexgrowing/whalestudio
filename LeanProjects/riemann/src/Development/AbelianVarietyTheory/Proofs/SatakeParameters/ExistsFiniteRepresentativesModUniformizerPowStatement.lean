import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteRepresentativesModUniformizerPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_representatives_mod_uniformizerPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
  Formalism.UG.IsUnramInv ϖ σ q → ∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧
    ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K := by
  first | exact @GlobalTheory.UnramReps.exists_reps_mod_pow | exact GlobalTheory.UnramReps.exists_reps_mod_pow | (intros; apply GlobalTheory.UnramReps.exists_reps_mod_pow <;> assumption)
