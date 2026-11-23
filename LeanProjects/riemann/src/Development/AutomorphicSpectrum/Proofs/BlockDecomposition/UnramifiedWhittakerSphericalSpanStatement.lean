import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerSphericalSpan
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_whittaker_spherical_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (ψ₀ : AddChar F ℂ), (∀ x ∈ 𝒪[F], ψ₀ x = 1) → (∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) → ∀ (z : Fin n → ℂˣ) (W : GL (Fin n) F → ℂ), W ∈ Submodule.span ℂ {f : GL (Fin n) F → ℂ | ∃ h : GL (Fin n) F, f = fun g => Spherical.sphericalWhittaker ψ₀ z (g * h)} → (∀ g, ∀ k ∈ GLnLocal.integralGL F n, W (g * k) = W g) → ∀ g, W g = W 1 * Spherical.sphericalWhittaker ψ₀ z g := by
  first | exact @GlobalTheory.CompanionTheory.SphericalSpan.eq_mul_sphericalWhittaker | exact GlobalTheory.CompanionTheory.SphericalSpan.eq_mul_sphericalWhittaker | (intros; apply GlobalTheory.CompanionTheory.SphericalSpan.eq_mul_sphericalWhittaker <;> assumption)
