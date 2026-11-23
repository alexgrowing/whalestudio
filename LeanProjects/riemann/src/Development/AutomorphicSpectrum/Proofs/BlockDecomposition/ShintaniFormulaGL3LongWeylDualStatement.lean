import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShintaniFormulaGL3LongWeylDual
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
theorem _root_.GlobalTheory.T.shintani_formula_GL3_long_weyl_dual : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (a b : ℤ), Spherical.sphericalWhittaker ψ₀ z (GL2LocalData.w3 * GL2LocalData.tinv (dg (unifUnit F ^ a) (unifUnit F ^ b) 1)) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * Spherical.evalAt z (Spherical.schur ![0, -b, -a]) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.SphericalDual.spherical_whittaker_long_weyl3_transpose_inv | exact GlobalTheory.CompanionTheory.SphericalDual.spherical_whittaker_long_weyl3_transpose_inv | (intros; apply GlobalTheory.CompanionTheory.SphericalDual.spherical_whittaker_long_weyl3_transpose_inv <;> assumption)
