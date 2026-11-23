import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsRationalOfRational
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ConclusionZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem actAB_one_reG (e : γ ≃ β) {JA : Matrix α α E} {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e)
    (g : GlobalTheory.WeilM.UG c J) (w : Matrix α β E) :
    GlobalTheory.WeilM.actAB c ((1 : GlobalTheory.WeilM.UG c JA), reG c e h g) (w.submatrix id e) =
      (GlobalTheory.WeilM.actB c g w).submatrix id e := by
  simp only [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, reG_val, OneMemClass.coe_one, Units.val_one, Matrix.one_mul,
    Matrix.transpose_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ _ _ _

theorem continuous_reG [TopologicalSpace E] (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E}
    (h : J' = J.submatrix e e) : Continuous (reG c e h) := by
  unfold reG
  refine Continuous.subtype_mk ?_ _
  refine (Continuous.units_map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom ?_).comp continuous_subtype_val
  exact (continuous_id (X := Matrix β β E)).matrix_reindex e.symm e.symm

end Gen

section Read

variable {D : D7} [Invertible (2 : AF D.host.F)]

theorem dblD_rho_eq {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ψ : AddChar (AF D.host.F) ℂ) (w : Matrix (Fin T.rank) (Fin S.rank ⊕ Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (dblD _ co).rho ψ w = (ddr co).rho ψ (w.submatrix id finSumFinEquiv.symm) := by
  unfold GlobalTheory.WeilM.Darboux.rho ddr
  rw [reD_e, Matrix.submatrix_submatrix]
  simp

end Read

end GlobalTheory.DblSchr

namespace GlobalTheory.DblSchr

set_option maxHeartbeats 1000000 in

theorem isUSplitting_omdOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co)
            (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco ωd hωd omd₀ htr
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have r1 : ResEta D 1 (GlobalTheory.Doubling.dblSp S).rank := GlobalTheory.Core.Rk.IP.FockModel.resEta_one_dbl S rT
  have hξd := GlobalTheory.DblSchr.dblGram_xi D S JB ξ hξ
  have hrat := GlobalTheory.DblSchr.ddr_rat D S T JA JB ξ κ co hco
  obtain ⟨hpres, himpl⟩ := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hadm := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hunit := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hcont := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hom : ∀ g, omdOf omd₀ g = omd₀ (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) := fun _ => rfl
  refine { pres := ?_, impl := ?_, adm := ?_, unit := ?_, cont := ?_ }
  · intro g φ hφ
    rw [hom]
    exact hpres _ φ hφ
  · intro g w φ hφ
    have e1 := dblD_rho_eq co ψ w
    have e2 := dblD_rho_eq co ψ (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) g w)
    have e3 := himpl (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) (w.submatrix id finSumFinEquiv.symm) φ hφ
    have e4 := actAB_one_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (JA := incM D.host.F JA) (incM_JBd S JB) g w
    rw [e4] at e3
    rw [hom]
    exact (congrArg (fun f => omd₀ _ (f φ)) e1).trans (e3.trans (congrFun e2 _).symm)
  · intro g l hl
    rw [hom]
    exact hadm _ l hl
  · exact hunit.comp _
  · have hr := continuous_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB)
    have hp : Continuous fun g => ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)),
        reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB) g) := continuous_const.prodMk hr
    intro l hl φ hφ
    exact Continuous.congr ((hcont l hl φ hφ).comp hp) (fun g => rfl)

end GlobalTheory.DblSchr
