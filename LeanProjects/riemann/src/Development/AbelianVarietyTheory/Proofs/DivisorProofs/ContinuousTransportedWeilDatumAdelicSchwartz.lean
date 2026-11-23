import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimFinitePartsWeilOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorArchimedeanSliceSchwartzSeminormBounStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilOperatorGroupVariableStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical

namespace GlobalTheory.WeilCont

theorem continuous_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om → GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass D.host.F) om := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om htr
  have hfin := GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hpt := GlobalTheory.T.continuous_transportedWeilOperator_groupVariable D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hbd := GlobalTheory.T.weilOperator_archimedeanSlice_schwartzSeminorm_bounded D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hpres := (GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr).1
  refine GlobalTheory.WeilCont.isContOn_of_local D.host.F hfin (fun Φ hΦ y => ?_)
  choose s hs using fun p => GlobalTheory.WeilCont.exists_slice D.host.F (hpres p Φ hΦ) y
  refine ⟨s, continuous_iff_continuousAt.2 fun p0 => GlobalTheory.T.schwartz_continuousAt_of_continuousAt_apply_of_bounded s p0 (fun v => ?_) (fun k n => ?_), hs⟩
  · simp_rw [hs]
    exact (hpt Φ hΦ _).continuousAt
  · obtain ⟨C, hC⟩ := hbd Φ hΦ y p0 k n
    refine ⟨C, hC.mono fun p hp v => ?_⟩
    have e : (⇑(s p)) = fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y) := funext (hs p)
    rw [e]
    exact hp v

end GlobalTheory.WeilCont
