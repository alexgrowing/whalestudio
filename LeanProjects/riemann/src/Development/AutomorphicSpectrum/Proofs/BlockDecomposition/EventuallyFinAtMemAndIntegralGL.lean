import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import GroundTheory.AutomorphicForms.ReductionFinite
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.AdelicIntegral

theorem eventually_finAt_mem_and_integralGL :
    ∀ (S : Finset Pl) (g₀ : G2) (U : ∀ v : Pl, Set (GL (Fin 2) (Qv v))), (∀ v ∈ S, U v ∈ nhds (finAt v g₀)) →
  (∀ v ∉ S, finAt v g₀ ∈ integralGL (Qv v) 2) →
  ∀ᶠ g in nhds g₀, (∀ v ∈ S, finAt v g ∈ U v) ∧ ∀ v ∉ S, finAt v g ∈ integralGL (Qv v) 2 := by
  intro S g₀ U hU hint
  have h₁ : ∀ᶠ g in nhds g₀, ∀ v ∈ S, finAt v g ∈ U v :=
    (Filter.eventually_all_finset S).2 fun v hv =>
      (GroundTheory.Automorphic.Reduction.continuous_finAt v).continuousAt.eventually_mem (hU v hv)
  have h₂ : ∀ᶠ g in nhds g₀, ∀ v ∉ S, finAt v g ∈ integralGL (Qv v) 2 :=
    (GroundTheory.Automorphic.Reduction.isOpen_setOf_forall_not_mem_imp S).mem_nhds hint
  exact h₁.and h₂

end GlobalTheory.CompanionTheory.AdelicIntegral
