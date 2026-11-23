import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspTypeLiftApproxFockSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaThirdStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.UpCuspLift
theorem upward_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsCuspFun (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro hLC hPr D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint
  have haut := _root_.GlobalTheory.UpConjLift.upward_theta_lift_isSmoothAutomorphic hLC hPr D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint
  have hCA := hLC D hS G₀ Pl0 T A Ks R G hR hG
  refine GlobalTheory.CuspApproxCompact.isCuspFun_of_approx D _ _ haut.cont haut.left fun C hC δ hδ => ?_
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ :=
    _root_.GlobalTheory.T.twist_cuspType_lift_approx_fockSpace hLC hPr D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hint C hC δ hδ
  choose F' hF' hE using fun l => hCA.up i hi (f l) (hf l) (F l) (hF l)
  have hval := fun l => GlobalTheory.LowVanishObj.multT_apply_cusp R.θ _ _ _ (F' l) (hF' l) (G.ItU i (p l) (v l))
  have hc : Continuous (∑ l, F' l (G.ItU i (p l) (v l))) := by
    rw [Finset.sum_fn]
    exact continuous_finset_sum _ fun l _ => (hval l).1.cont
  have hl : ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g, (∑ l, F' l (G.ItU i (p l) (v l))) (γ * g) = (∑ l, F' l (G.ItU i (p l) (v l))) g := by
    intro γ hγ g
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => (hval l).1.left γ hγ g
  have hmem := fun l => (GlobalTheory.AutFunCompare.isCuspFun_iff _ _ (hval l).1.cont (hval l).1.left).1 (hval l).2
  refine ⟨∑ l, F' l (G.ItU i (p l) (v l)), hc, hl, ?_, ?_⟩
  · exact (GlobalTheory.AutFunCompare.isCuspFun_iff _ _ hc hl).2 (Submodule.sum_mem _ fun l _ => hmem l)
  · intro h hh
    have e : (∑ l, F' l (G.ItU i (p l) (v l))) h =
        ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g
          (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F l (v l) g ∂(G.mP i).ν := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun l _ => ((hE l (p l) (v l) h).2).symm
    rw [e]
    exact happ h hh
end GlobalTheory.UpCuspLift
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_upward_theta_lift_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsCuspFun (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @_root_.GlobalTheory.UpCuspLift.upward_theta_lift_isCuspidal | exact _root_.GlobalTheory.UpCuspLift.upward_theta_lift_isCuspidal | (intros; apply _root_.GlobalTheory.UpCuspLift.upward_theta_lift_isCuspidal <;> assumption)
end
