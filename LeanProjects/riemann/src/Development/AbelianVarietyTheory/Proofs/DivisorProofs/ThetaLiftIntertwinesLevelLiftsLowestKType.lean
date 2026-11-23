import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShift

open GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem smul_apply_of_eq {H W : Type} [AddCommGroup W] [Module ℂ W] (c : ℂ) (hc : c ≠ 0) (f : H → W) (h : H) (w : W)
    (hw : f h = c⁻¹ • w) : (c • f) h = w := by
  rw [Pi.smul_apply, hw, smul_inv_smul₀ hc]

theorem pt_shift (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : κ ∈ GfC (Vc D i)) (hκ' : κ' ∈ GfC (Wc D i)) (a : ℂ)
    (hv : R.ωP i t (κ, κ') (R.vP i t) = a • R.vP i t) :
    ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = a • R.ptP i t P :=
  GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hM.inf (hP.ωP i t) _ _ _ _ _
    (hP.pt_theta i t) κ hκ κ' hκ' a hv

theorem thF_shift_of_eigen (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0)
    (g0 : G0 R.Pg D.R.r)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (y y' : (R.HV i t).H) (c : ℂ) (hc0 : c ≠ 0)
    (hpt : ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = c⁻¹ • R.ptP i t P)
    (hy : ∀ h, (c • R.extV i t y') h = R.extV i t y (h * κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)) :
    R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  refine (hP.thF i t).elim fun thP hPF => ?_
  have hker := fun P => GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hP.ωP i t)
    (R.ptP i t P) (hP.pt_theta i t P)
  have hm := thetaLift_shift hPF.1 (GQ (Vc D i)) κ κ' c hc0
    (integral_shift (Vc D i) (R.βV i) (R.datVt i t) g0 κ hκ (R.νV i t) (hM.νV i t).1.1 (R.fdV i t)
      (hM.νV i t).2)
    (fun P γ hγ g h => by
      have := (hker P).1 γ hγ 1 (GQ (Wc D i)).one_mem h g
      rwa [one_mul] at this)
    (fun P g h => (hker P).2 κ κ' c⁻¹ (hpt P) h g)
    ((R.extV i t).rangeRestrict y) ((R.extV i t).rangeRestrict y')
    (extV_left R hM.HV i t y)
    hy
    (PiTensorProduct.tprod ℂ v) x
  exact (congrFun (hPF.2 y' v) x).trans (hm.trans (congrFun (hPF.2 y v) (x * κ')).symm)

theorem thF_shift_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)), R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hM hP i t g0 κ κ' hκ hκ' y y' hy v x
  have hc0 := levChi_ne_zero (V := Vc D i) (β := R.βV i) (flagL (R.datVt i t)) κ
  exact thF_shift_of_eigen R hM hP i t g0 κ κ' hκ y y' (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ) hc0
    (pt_shift R hM hP i t κ κ' hκ.1 hκ'.1 _ (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hlev hM.inf hP.ωP hP.vP i t g0 κ κ' hκ hκ'))
    (fun h => smul_apply_of_eq _ hc0 _ h _ (hy h)) v x

end GlobalTheory.ThetaShift

end
