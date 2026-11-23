import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CauchyIdentitySchurGL3GL2
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
theorem _root_.GlobalTheory.T.cauchy_identity_schur_GL3_GL2 : ∀ (x : Fin 3 → ℂˣ) (y : Fin 2 → ℂˣ) (X : ℂ), (∀ i, ‖(x i : ℂ)‖ = 1) → (∀ j, ‖(y j : ℂ)‖ = 1) → ‖X‖ < 1 → HasSum (fun p : ℕ × ℕ => Spherical.evalAt x (Spherical.schur ![((p.1 + p.2 : ℕ) : ℤ), (p.2 : ℤ), 0]) * Spherical.evalAt y (Spherical.schur ![((p.1 + p.2 : ℕ) : ℤ), (p.2 : ℤ)]) * X ^ (p.1 + 2 * p.2)) (∏ i, ∏ j, (1 - (x i : ℂ) * (y j : ℂ) * X)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.CauchyUnit.cauchy_unit | exact GlobalTheory.CompanionTheory.CauchyUnit.cauchy_unit | (intros; apply GlobalTheory.CompanionTheory.CauchyUnit.cauchy_unit <;> assumption)
