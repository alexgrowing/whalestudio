import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacuumPairingPolynomialTranslatesScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.FactorInf

theorem fockVac_om_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D}
    (hθ : IsInfFam θ) {γ : GA D T} (hγ : γ ∈ GfC T) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ J f) :
    IsFockVacAt (heisO ψ S T) θ τ J (om (1, γ) f) := by
  have e : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, compAt θ τ (mt T γ) * z * compAt θ τ (mt S (1 : GA D S)⁻¹) = z := fun z => by
    rw [inv_one, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hγ τ,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (Subgroup.one_mem _) τ, Matrix.one_mul, Matrix.mul_one]
  intro z
  have h := congrArg (om (1, γ)) (hv z)
  unfold annih at h ⊢
  rw [map_add, map_smul, GlobalTheory.OrientedHeis.om_dRho hom hθ 1 γ τ z hf, GlobalTheory.OrientedHeis.om_dRho hom hθ 1 γ τ (J z) hf,
    e, e, map_zero] at h
  exact h

theorem factInf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FactInf R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ u hu γ hγ P P'
  have hW := hL.thP.ωP i t
  have hθ : IsInfFam R.θ := hL.models.inf
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP at this
    rwa [GlobalTheory.FiniteFock.pureTensorO_one] at this
  have hvac : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hL.thP.vP i t) hth
  set f₁ := R.ωP i t (1, γ) (R.vP i t) with hf₁
  have hth1 : IsThetaFunO R.ψ (Vc D i) (Wc D i) f₁ := hW.om_pres _ _ hth
  have hvac1 : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) f₁ :=
    fun τ => fockVac_om_fin hW hθ hγ τ _ hth (hvac τ)
  have hmul : R.ωP i t (1, u * γ) (R.ptP i t P) = R.ωP i t (1, u) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
      (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f₁ P) := by
    have e : ((1 : GA D (Vc D i)), u * γ) = (1, u) * (1, γ) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    congr 1
    unfold RealDat.ptP
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW R.θ hθ 1 (Subgroup.one_mem _) γ hγ _ _ _ _ _ P hth
  obtain ⟨c, hc⟩ := GlobalTheory.T.fockVacuum_pairing_polynomial_translates_scalar D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank)
    (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => isCartanInv_one_of_onb (hL.models.BV i τ))
    (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hL.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hL.models.order i τ)) μ 𝓕 hμ u hu P P'
  have hne := (vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ).1
  rw [hmul]
  unfold RealDat.ptP
  rw [hc f₁ _ hth1 hth hvac1 hvac, hc _ _ hth hth hvac hvac]
  unfold coef
  rw [← hf₁]
  field_simp

end GlobalTheory.RawLift.FactorInf
