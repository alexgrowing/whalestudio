import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowth
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstantStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_lie_word_growth : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Q : M → M → ℂ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hpos : ∀ x, x ≠ 0 → 0 < (Q x x).re) {d : ℕ} (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (A : ℝ) (hA : 0 ≤ A) (hs : ∀ i x, |2 * (Q (X i x) x).re| ≤ A * (Q x x).re) (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V), ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V, Real.sqrt (Q ((l.map X).prod u) ((l.map X).prod u)).re ≤ C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q u u).re := by
  first | exact @GlobalTheory.CompanionTheory.HCForm.nelson_form | exact GlobalTheory.CompanionTheory.HCForm.nelson_form | (intros; apply GlobalTheory.CompanionTheory.HCForm.nelson_form <;> assumption)
