import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerMemSphericalSpan
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_whittaker_mem_spherical_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → IsUnramifiedChar c₁ → IsUnramifiedChar c₂ → ∀ Φ : F × F → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → GL2LocalData.WcS χ c₁ c₂ Φ ∈ Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] (g * h)} := by
  first | exact @GlobalTheory.CompanionTheory.WS.WcS_mem_span | exact GlobalTheory.CompanionTheory.WS.WcS_mem_span | (intros; apply GlobalTheory.CompanionTheory.WS.WcS_mem_span <;> assumption)
