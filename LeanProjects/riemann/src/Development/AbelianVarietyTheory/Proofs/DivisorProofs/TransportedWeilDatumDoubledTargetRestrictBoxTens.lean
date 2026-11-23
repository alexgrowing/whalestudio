import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledCoordsBoxProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagActsOnExternalProductStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblRestrict

set_option maxHeartbeats 2000000 in

theorem omp_diag_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ),
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
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ωd omp →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ))),
            gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              omp (gd, 1) (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  let h : GA D T := ⟨g.1, GlobalTheory.ThetaTransform.mem_GA_target hA g⟩
  let hd : GA D (GlobalTheory.Doubling.dblSp T) := ⟨gd.1, GlobalTheory.ThetaTransform.mem_GA_target rfl gd⟩
  have hh : Formalism.L2.Theta.mt T h = g.1.1 := rfl
  have hhd : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd = gd.1.1 := rfl
  have h1S : Formalism.L2.Theta.mt S 1 = ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))⁻¹).1.1ᵀ := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨hB1, hΘ1⟩ := hom g 1 1 h hh h1S φ₁ hφ₁
  have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨hA1, hΘA⟩ := homp gd 1 1 hd hhd h1S _ hbox
  have hφ₂' := GlobalTheory.ConjSch.star_mem_schA κ φ₂ hφ₂
  have bij := GlobalTheory.ThetaTransform.thetaTr_bij co hψ hA hB hrat
  have bijd := GlobalTheory.ThetaTransform.thetaTr_bij (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) hψ rfl hB
    (GlobalTheory.WeilSchrodinger.DblTarget.coDbl_rat hA co hrat)
  refine bijd.2.1 _ hA1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ hB1 φ₂ hφ₂) ?_
  have e1 := GlobalTheory.T.thetaTransform_doubledCoords_boxProduct D ψ hψ S T JA JB ξ hA κ co _ hφ₁ _ hφ₂
  have e2 := GlobalTheory.T.thetaTransform_doubledCoords_boxProduct D ψ hψ S T JA JB ξ hA κ co _ hB1 _ hφ₂
  have hgd' : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) := hgd
  have key := GlobalTheory.T.doubledWeilDatum_diag_acts_on_externalProduct D ψ hψ S T χS χT ω hω ωd hωd (GlobalTheory.T.doubledWeilDatum_diag_thetaProduct_eq_scalar_smul D ψ hψ S T χS χT ω hω ωd hωd) h hd hgd' _ _
    ((bij.2.2 _).2 ⟨φ₁, hφ₁, rfl⟩) ((bij.2.2 _).2 ⟨_, hφ₂', rfl⟩)
  refine hΘA.trans ?_
  refine ((congrArg (ωd (1, hd)) e1).trans key).trans ?_
  refine Eq.trans ?_ e2.symm
  rw [hΘ1]

end GlobalTheory.WeilSchrodinger.DblRestrict

end
