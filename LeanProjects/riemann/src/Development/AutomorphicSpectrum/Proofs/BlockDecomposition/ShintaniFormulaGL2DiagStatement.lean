import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShintaniFormulaGL2Diag
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_formula_GL2_diag : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (y : Fin 2 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ y (d2 (unifUnit F ^ a) (unifUnit F ^ b)) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * Spherical.evalAt y (Spherical.schur ![a, b]) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.ZU.SphericalWhittakerGL2.spherical_whittaker_GL2_uniformizer_diag | exact GlobalTheory.CompanionTheory.GL2Factorization.ZU.SphericalWhittakerGL2.spherical_whittaker_GL2_uniformizer_diag | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.ZU.SphericalWhittakerGL2.spherical_whittaker_GL2_uniformizer_diag <;> assumption)
