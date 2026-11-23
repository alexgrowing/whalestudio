import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticResidueCard
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_residue_card : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → residueCard E = residueCard F ^ 2 → ∀ χ : AddChar F Circle, IsStd χ → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) → ∀ c : Eˣ →* ℂˣ, IsUnit1 c → IsUnramifiedChar c → ∀ b : ℂˣ, b ^ 2 = c (Units.map (algebraMap F E).toMonoidHom (unifUnit F)) → ∀ Φ ∈ GL2LocalData.SBc F E c, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) (GL2LocalData.lamE E χ η) c Φ ∈ Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![b, -b] (g * h)} := by
  first | exact @GlobalTheory.CompanionTheory.WInert.winert_span | exact GlobalTheory.CompanionTheory.WInert.winert_span | (intros; apply GlobalTheory.CompanionTheory.WInert.winert_span <;> assumption)
