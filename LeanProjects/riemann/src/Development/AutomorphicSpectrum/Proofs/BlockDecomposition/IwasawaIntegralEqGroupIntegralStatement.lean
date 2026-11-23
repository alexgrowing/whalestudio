import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralEqGroupIntegral
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_integral_eq_group_integral : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ), Φ ∈ LFS.SB F →
  ∀ p : Fˣ × Fˣ × GL (Fin 2) F, p.2.2 ∈ K2 F →
    iw (LFS.Wp ψ W₀ Φ) W' s p = ∫ g, Aq ψ W₀ W' Φ s (p, g) ∂LFS.hG ψ := by
  first | exact @GlobalTheory.CompanionTheory.GL2Unfolding.Ptw.main | exact GlobalTheory.CompanionTheory.GL2Unfolding.Ptw.main | (intros; apply GlobalTheory.CompanionTheory.GL2Unfolding.Ptw.main <;> assumption)
