import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialCharacterExtension
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerBoundQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCharacterTwistNontrivialGaloisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialGaloisIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenNormImageUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuityQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasureIndependenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNonvanishingCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasurabilityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerIntegrableQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuousQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportBoundQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerCentralTwistStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_nontrivial_character_extension : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ : E → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ∀ h₀ : GL (Fin 2) F, ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, (k * h₀).val 1 0 ≠ 0 → ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤ C * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) ∧ (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ B) := by
  first | exact @GlobalTheory.CompanionTheory.WhitOffBorel.whittaker_off_borel | exact GlobalTheory.CompanionTheory.WhitOffBorel.whittaker_off_borel | (intros; apply GlobalTheory.CompanionTheory.WhitOffBorel.whittaker_off_borel <;> assumption)
