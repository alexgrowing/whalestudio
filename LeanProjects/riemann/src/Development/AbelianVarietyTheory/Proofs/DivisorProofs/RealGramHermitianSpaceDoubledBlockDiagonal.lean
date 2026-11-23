import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumFirstFactorOnDoublingTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInjOnAdelicSchwartzSpaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblRestr

open GlobalTheory.Doubling GlobalTheory.DblSchr GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero Formalism.IndefR.Datum

theorem partner_dbl {D : D7} (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
    (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (hgd : gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1) (gs : GA D S) (hgs : mt S gs = (g⁻¹).1.1ᵀ)
    (gdd : GA D (dblSp S)) (hgdd : mt (dblSp S) gdd = ((reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)⁻¹).1.1ᵀ) :
    gdd = io S (gs, 1) := by
  have hg1 : g.1.1 * (g⁻¹).1.1 = 1 := Units.mul_inv g.1
  have hinv : (gd⁻¹).1.1 = Matrix.fromBlocks (g⁻¹).1.1 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hgd, Matrix.fromBlocks_multiply, hg1]
    simp [Matrix.fromBlocks_one]
  have hr : ((reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)⁻¹).1.1 =
      (Matrix.fromBlocks (g⁻¹).1.1 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← map_inv, reG_val, hinv]
  have hm3 : mt (dblSp S) (io S (gs, 1)) =
      (Matrix.fromBlocks (mt S gs) 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  have hm : mt (dblSp S) gdd = mt (dblSp S) (io S (gs, 1)) := by
    rw [hgdd, hr, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, ← hgs, hm3, Matrix.transpose_zero,
      Matrix.transpose_one]
  exact Subtype.ext (Units.ext hm)

theorem restr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
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
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
            gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              GlobalTheory.DblSchr.omdOf omd₀ gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omd₀ homd g gd hgd φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨gs, h1, hh1, hgs⟩ := GlobalTheory.T.unitaryPair_partner_inverse_transpose D S T JA JB ξ hA hB 1 g
  have h1e : h1 = 1 := Subtype.ext (Units.ext (hh1.trans rfl))
  obtain ⟨gdd, h2, hh2, hgdd⟩ := GlobalTheory.T.unitaryPair_partner_inverse_transpose D (dblSp S) T JA (JBd S JB) ξ hA (dblGram_xi D S JB ξ hB) 1
    (reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)
  have h2e : h2 = 1 := Subtype.ext (Units.ext (hh2.trans rfl))
  have hgdd' : gdd = io S (gs, 1) := partner_dbl S JB g gd hgd gs hgs gdd hgdd
  subst h1e h2e hgdd'
  have t1 := hom 1 g gs 1 hh1 hgs φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  have t2 := homd 1 (reG _ finSumFinEquiv.symm (incM_JBd S JB) gd) (io S (gs, 1)) 1 hh2 hgdd _ hΦ
  have hφ₂' := GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection D.host.F κ φ₂ hφ₂
  have th₁ := GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ S T JA JB ξ hA hB κ co hrat φ₁ hφ₁
  have th₂ := GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ S T JA JB ξ hA hB κ co hrat _ hφ₂'
  have key := t2.2.trans ((congrArg (ωd (io S (gs, 1), 1)) (GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj D ψ hψ S T JA JB ξ κ co φ₁ hφ₁ φ₂ hφ₂)).trans
    ((GlobalTheory.T.doubledWeilDatum_firstFactor_on_doublingTensor D ψ hψ S T χS χT ω hω ωd hωd gs _ _ th₁ th₂).trans
      ((congrArg (fun f => GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f
        (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj D ψ hψ S T JA JB ξ κ co _ t1.1 φ₂ hφ₂).symm)))
  refine GlobalTheory.T.thetaTransform_injOn_adelicSchwartzSpace D ψ hψ (κ ⊕ κ) _ t2.1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ t1.1 φ₂ hφ₂) fun w => ?_
  have := congrFun key ((ddr co).e.symm w)
  simpa only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] using this

end GlobalTheory.DblRestr

end
