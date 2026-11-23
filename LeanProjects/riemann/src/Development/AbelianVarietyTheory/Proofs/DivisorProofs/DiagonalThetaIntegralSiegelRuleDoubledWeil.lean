import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLEpsPairMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryInvTransposeOfScaledInverseGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelParabolicConjInvTransposeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem ddr_rat : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  intro D S T JA JB ξ κ _ co hco x
  obtain ⟨y₁, z₁, h₁⟩ := hco ((x.submatrix id finSumFinEquiv).toCols₁)
  obtain ⟨y₂, z₂, h₂⟩ := hco ((x.submatrix id finSumFinEquiv).toCols₂)
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  have e : (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
      (Sum.elim (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁)).1
          (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂)).1,
        Sum.elim (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁)).2
          (-(co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂)).2)) := rfl
  rw [e, h₁, h₂]
  ext (i | i) <;> simp

theorem actO_epsD_lagr : ∀ (D : D7) (S T : HSp D) (w : WO S T),
    actO (dblSp S) T (epsD S)⁻¹ 1 (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w) = GlobalTheory.DiagSiegel.diagMat w := by
  intro D S T w
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w = (Matrix.fromCols w (-w)).submatrix id finSumFinEquiv.symm := by
    ext i j
    rcases h : finSumFinEquiv.symm j with k | k <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, h]
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by simp [Formalism.L2.Theta.mt]
  unfold actO
  rw [inv_inv, h1, Matrix.one_mul, mt_epsD, hl, blkMat, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp [GlobalTheory.DiagSiegel.diagMat]

theorem epsD_mem_GQ : ∀ (D : D7) (S : HSp D), epsD S ∈ GQ (dblSp S) := by
  intro D S
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2
    ⟨blkGL finSumFinEquiv ((1, -1) : GL (Fin S.rank) D.host.E × GL (Fin S.rank) D.host.E), ?_, ?_⟩)
  · rw [show (dblSp S).gram = blkMat finSumFinEquiv S.gram (-S.gram) from gram_hdbl S, blkGL_mem_UJ]
    exact ⟨one_mem _, neg_one_mem_UJ _ _⟩
  · rw [bc_blkGL]
    apply Units.ext
    show blkMat finSumFinEquiv _ _ = blkMat finSumFinEquiv (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (-1)
    simp [Formalism.UG.bc]

theorem rat_act : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V T : HSp D) (χV χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D T →* Module.End ℂ (WO V T → ℂ)), IsWeilDatumO ψ V T χV χT ω →
    ∀ γ ∈ GQ V, ∀ f, IsThetaFunO ψ V T f → ∀ x, ω (γ, 1) f x = f (actO V T γ⁻¹ 1 x) := by
  intro D ψ V T χV χT ω hW γ hγ f hf x
  have hx : actO V T γ 1 (actO V T γ⁻¹ 1 x) = x := by
    simp only [actO, Formalism.L2.Theta.mt, map_one, Units.val_one, Matrix.one_mul, inv_inv, Matrix.mul_assoc,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, Matrix.mul_one]
  have e1 : ∀ (g : WO V T → ℂ) (y : WO V T), heisO ψ V T y g 0 = g y := by
    intro g y
    have h0 : symplOH V T 0 y = 0 := by simp [symplOH, symplO, hO]
    simp only [heisO, zero_add, h0, AddChar.map_zero_eq_one, one_mul]
  calc ω (γ, 1) f x = heisO ψ V T x (ω (γ, 1) f) 0 := (e1 _ _).symm
    _ = heisO ψ V T (actO V T γ 1 (actO V T γ⁻¹ 1 x)) (ω (γ, 1) f) 0 := by rw [hx]
    _ = ω (γ, 1) (heisO ψ V T (actO V T γ⁻¹ 1 x) f) 0 := by rw [← hW.om_heis γ 1 _ f hf]
    _ = heisO ψ V T (actO V T γ⁻¹ 1 x) f 0 :=
      hW.om_aut γ hγ 1 (one_mem _) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf _)
    _ = f (actO V T γ⁻¹ 1 x) := e1 _ _

theorem exists_transpose_inv : ∀ (D : D7) (V : HSp D) (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), ξ • incM D.host.F J = incM D.host.F (D.host.xi0 • V.gram⁻¹) →
    ∀ b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F J),
      ∃ g : GA D V, Formalism.L2.Theta.mt V g = (b⁻¹).1.1ᵀ := GlobalTheory.T.exists_unitary_invTranspose_of_scaledInverseGram

theorem siegel_conj : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
    p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
    ∀ g : GA D (GlobalTheory.Doubling.dblSp S), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ →
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := GlobalTheory.T.exists_siegelParabolic_conj_invTranspose

theorem chi_conj : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D χ n → ∀ z : (AE D)ˣ,
    χ (conjUnit D.sp.cm.sig z) = (χ z)⁻¹ := by
  intro D χ n h z
  have := congrArg (fun m : (AE D)ˣ →* Circle => m z) (comp_conjUnit_eq_inv h)
  simpa using this

theorem absA_conj : ∀ (D : D7) (z : (AE D)ˣ), absA D (conjUnit D.sp.cm.sig z) = absA D z :=
  fun _ z => absE_conjUnit _ z

theorem absA_eq_modu : ∀ (D : D7) (z : (AE D)ˣ),
    absA D z = (GlobalTheory.WeilM.adeleClass D.host.F).modu (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) z) :=
  fun D z => (GlobalTheory.ModuAdele.modu_norm_eq_absE D.host.F D.host.E z).symm

end GlobalTheory.DiagThetaRule

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem scalar_rule (D : D7) (S T : HSp D) (χT : (AE D)ˣ →* Circle) (hrT : ResEta D χT T.rank)
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    ((χT⁻¹ (conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t)) : Circle) : ℂ) *
        npow (absA D (conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t))) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero S T + (S.rank : ℂ) / 2) =
      GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χT
        (Fintype.card (Fin T.rank)) t := by
  rw [MonoidHom.inv_apply, chi_conj D χT T.rank hrT, inv_inv, absA_conj, absA_eq_modu]
  unfold GlobalTheory.DiagSiegel.ruleFac GlobalTheory.Doubling.npow GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero
  rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  congr 2
  rw [Fintype.card_fin]
  push_cast
  ring

end GlobalTheory.DiagThetaRule

namespace GlobalTheory.DiagThetaRule
set_option maxHeartbeats 1000000 in

theorem thetaDiagInt_omdOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
            ResEta D χS S.rank → ResEta D χT T.rank →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
            (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
            p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
          ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
            GlobalTheory.DblSchr.omdOf omd₀ p Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ) ∧
            GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ
                         (GlobalTheory.DblSchr.omdOf omd₀ p Φ)) =
              GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χT (Fintype.card (Fin T.rank)) t *
                GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hco ν 𝓕 hν χS χT hχS hχT hrS hrT ωd hW omd₀ hTr p t hpt Φ hΦ
  have hBd := GlobalTheory.DblSchr.dblGram_xi D S JB ξ hB
  obtain ⟨g', hg'⟩ := exists_transpose_inv D (GlobalTheory.Doubling.dblSp S) (GlobalTheory.DblSchr.JBd S JB) ξ hBd
    (GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) =
      (1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)).1.1 := by
    simp [Formalism.L2.Theta.mt]
  have key := hTr 1 _ g' 1 h1 hg' Φ hΦ
  refine ⟨key.1, ?_⟩
  rw [show GlobalTheory.DblSchr.omdOf omd₀ p = omd₀ (1, GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm
    (GlobalTheory.DblSchr.incM_JBd S JB) p) from rfl, key.2]
  have hf : Formalism.IndefR.Datum.IsThetaFunO ψ (GlobalTheory.Doubling.dblSp S) T
      (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) :=
    GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ (GlobalTheory.Doubling.dblSp S) T JA (GlobalTheory.DblSchr.JBd S JB) ξ hA hBd (κ ⊕ κ) (GlobalTheory.DblSchr.ddr co)
      (ddr_rat D S T JA JB ξ κ co hco) Φ hΦ
  have hdiag : ∀ F, Formalism.IndefR.Datum.IsThetaFunO ψ (GlobalTheory.Doubling.dblSp S) T F →
      GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 F = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec S T ωd ν 𝓕 F (epsD S) := by
    intro F hF
    show ∫ w in 𝓕, F (GlobalTheory.DiagSiegel.diagMat w) ∂ν =
      ∫ w in 𝓕, ωd (epsD S, 1) F (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w) ∂ν
    congr 1
    funext w
    rw [rat_act D ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd hW (epsD S) (epsD_mem_GQ D S) F hF, actO_epsD_lagr]
  obtain ⟨h, hεg, haP⟩ := siegel_conj D S JB p t hpt g' hg'
  have hlaw := GlobalTheory.Core.Rk.SWLaw.swSec_law GlobalTheory.weilRepresentationUnitaryPair D ψ S T χT ωd hW ν 𝓕 hν _ hf h (epsD S)
  have e1 : GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (ωd (g', 1) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec S T ωd ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) (epsD S * g') := by
    rw [hdiag _ (hW.om_pres _ _ hf)]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e1, hεg, hlaw, ← hdiag _ hf, haP]
  exact congrArg (· * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ))
    (scalar_rule D S T χT hrT t)
end GlobalTheory.DiagThetaRule

end
