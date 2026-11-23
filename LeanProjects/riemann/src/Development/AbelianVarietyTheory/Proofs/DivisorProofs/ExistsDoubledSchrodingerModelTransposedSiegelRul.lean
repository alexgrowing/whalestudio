import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleTransportedWeilDatumDoubledTargetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTensStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchrodinger.DblTarget

set_option maxHeartbeats 1000000

theorem exists_dbl_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
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
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JA))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JB) (incM D.host.F JA)
                           (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JB) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) dd χS (GlobalTheory.WeilM.diagCols (Fin T.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom
  have h1S := isHeckeChar_one (D := D)
  have r1 := resEta_one_dblSp T rT
  obtain ⟨ωd, hωd⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ S (GlobalTheory.Doubling.dblSp T) χS 1 hψ hS h1S rS r1
  have hrat' := coDbl_rat hA co hrat
  obtain ⟨omp, hmp⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ S (GlobalTheory.Doubling.dblSp T) χS 1 hS h1S rS r1 _ JB ξ rfl hB (κ ⊕ κ)
    (coDbl hA co) hrat' ωd hωd omp hmp
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (coDbl hA co)
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) omp := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hsg := GlobalTheory.T.siegelRule_transported_weilDatum_doubledTarget D ψ hψ S T χS hS rS JB ξ hB (κ ⊕ κ) (coDbl hA co) hrat' ωd hωd omp hmp
  have t1 := isDblCoord_transD co
  have t2 : GlobalTheory.WeilM.IsLagr (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))
      (GlobalTheory.WeilM.diagCols (Fin T.rank)) := GlobalTheory.WeilM.isLagr_diagCols _ _
  have t4 : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (transD _ (dblRows co)) (GlobalTheory.WeilM.actB _)
      ((omp.comp (MonoidHom.inl _ _)).comp (ugDbl T hA)) :=
    isUSplitting_reindex finSumFinEquiv (dblRows co) _ (reindex_dbl_incM T hA) (isUSplitting_inl hsp)
  have t5 : GlobalTheory.WeilM.SiegelRule _ (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JB) _ (transD _ (dblRows co)) χS
      (GlobalTheory.WeilM.diagCols (Fin T.rank)) ((omp.comp (MonoidHom.inl _ _)).comp (ugDbl T hA)) :=
    siegelRule_reindex finSumFinEquiv (dblRows co) _ (reindex_dbl_incM T hA) χS _ hsg
  refine ⟨_, _, t1, ⟨t2, t4, t5⟩, ?_⟩
  intro g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have key := GlobalTheory.T.transportedWeilDatum_doubledTarget_restrict_boxTensor D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom ωd hωd omp hmp
    g (ugDbl T hA gd) (by rw [ugDbl_coe, hgd]) φ₁ hφ₁ φ₂ hφ₂
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply]
  exact key

end GlobalTheory.WeilSchrodinger.DblTarget

end
