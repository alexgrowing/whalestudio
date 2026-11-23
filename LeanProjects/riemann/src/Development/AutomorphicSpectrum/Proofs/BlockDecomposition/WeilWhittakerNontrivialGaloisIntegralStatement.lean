import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialGaloisIntegral
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_whittaker_nontrivial_galois_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E), σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (Φ : E → ℂ) (a b cc d : F), cc ≠ 0 → ∀ t : Eˣ, GL2LocalData.rW χ σ μ lam a b cc d (fun x => Φ (x * (t : E))) 1 = lam * GL2LocalData.nsg E (-cc) * (((modulus cc : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus (t : E) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (a / cc) : ℂ) * gaussI χ μ Φ (d / (cc * Algebra.norm F (t : E))) ((algebraMap F E cc)⁻¹ * (t : E)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.WcB.RwFormula.rW_one_eq_gaussI | exact GlobalTheory.CompanionTheory.WcB.RwFormula.rW_one_eq_gaussI | (intros; apply GlobalTheory.CompanionTheory.WcB.RwFormula.rW_one_eq_gaussI <;> assumption)
