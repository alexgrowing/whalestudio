import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWhittakerLeftUnipotent
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_whittaker_left_unipotent : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (v g : GL (Fin 2) F), v ∈ Iwasawa.unipotent F 2 → GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ (v * g) = Whittaker.psiN (Circle.coeHom.compAddChar χ) v * GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ g := by
  first | exact @GlobalTheory.CompanionTheory.WS.WL_unipotent_left | exact GlobalTheory.CompanionTheory.WS.WL_unipotent_left | (intros; apply GlobalTheory.CompanionTheory.WS.WL_unipotent_left <;> assumption)
