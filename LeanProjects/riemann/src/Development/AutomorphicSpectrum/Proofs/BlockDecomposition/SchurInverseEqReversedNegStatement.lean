import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurInverseEqReversedNeg
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
theorem _root_.GlobalTheory.T.schur_inverse_eq_reversed_neg : ∀ (n : ℕ) (z : Fin n → ℂˣ) (l : Fin n → ℤ), Spherical.evalAt (fun i => (z i)⁻¹) (Spherical.schur l) = Spherical.evalAt z (Spherical.schur (fun i => -l (Fin.rev i))) := by
  first | exact @GlobalTheory.CompanionTheory.SchurDual.evalAt_inv_schur | exact GlobalTheory.CompanionTheory.SchurDual.evalAt_inv_schur | (intros; apply GlobalTheory.CompanionTheory.SchurDual.evalAt_inv_schur <;> assumption)
