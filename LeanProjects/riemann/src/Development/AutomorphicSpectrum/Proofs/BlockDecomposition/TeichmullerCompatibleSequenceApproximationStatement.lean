import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCompatibleSequenceApproximation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_compatible_sequence_approximation : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ Z : ℕ → ℂ_[l],
    (∀ n, ‖Z n‖ ≤ 1) → (∀ n, ‖Z (n + 1) ^ l ^ f - Z n‖ ≤ ρ) →
    ∃ u : ℕ → Tl l, (∀ n, u (n + 1) ^ l ^ f = u n) ∧ ∀ n, ‖sh (u n) - Z n‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat <;> assumption)
