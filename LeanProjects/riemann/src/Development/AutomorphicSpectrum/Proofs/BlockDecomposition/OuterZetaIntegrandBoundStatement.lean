import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OuterZetaIntegrandBound
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.outer_zeta_integrand_bound : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ) (C₀ C₁ C₂ B R ε : ℝ),
  0 ≤ C₀ → 0 ≤ C₁ → 0 ≤ C₂ → 0 < ε → ε < 1 / 2 →
  (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) →
  (∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, ‖W₀ (dg2 a 1 * k)‖ ≤ C₀ * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
    (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)) →
  (∀ h : GL (Fin 2) F, ‖W' h‖ ≤ C₁ * ((modulus (h.val).det : ℝ) / mx (e2r h) ^ 2) ^ (1 / 2 - ε)) →
  (∀ A ξ, ‖pFT ψ Φ A ξ‖ ≤ C₂ ∧ (pFT ψ Φ A ξ ≠ 0 → (∀ i j, (modulus (A i j) : ℝ) ≤ R) ∧ mx ξ ≤ R)) →
  ∀ (g : GL (Fin 2) F) (p : Fˣ × Fˣ × GL (Fin 2) F), p.2.2 ∈ K2 F →
    ‖Bq ψ W₀ W' Φ s g (hI p)‖ ≤ C₀ * C₁ * C₂ * Mj R B s.re ε g p := by
  first | exact @GlobalTheory.CompanionTheory.GL2Unfolding.PtB.main | exact GlobalTheory.CompanionTheory.GL2Unfolding.PtB.main | (intros; apply GlobalTheory.CompanionTheory.GL2Unfolding.PtB.main <;> assumption)
