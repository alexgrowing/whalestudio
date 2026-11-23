import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.TTRANS
import GroundTheory.AutomorphicForms.ReductionFinite
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.AdelicIntegral

theorem exists_finset_finAt_mem_integralGL :
    ∀ h : Ad3.R.G2, ∃ S : Finset Ad3.Pl, ∀ v ∉ S,
      GroundTheory.Automorphic.Reduction.finAt v h ∈ GroundTheory.Automorphic.GLnLocal.integralGL (Ad3.Qv v) 2 := by
  intro h
  obtain ⟨S, hS⟩ := GroundTheory.Automorphic.Reduction.exists_finite_forall_mem_integralGL
    (isCompact_singleton (x := h))
  exact ⟨S, fun v hv => hS h rfl v hv⟩

end GlobalTheory.CompanionTheory.AdelicIntegral
