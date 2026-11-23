import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thF_shift_core (R : RealDat D A Ks) (F : Face D A) (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) (g0 : G0 R.Pg D.R.r)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (hκ' : κ' ∈ GfC (Wc D i)) (y y' : (R.HV i t).H) (c : ℂ) (hc0 : c ≠ 0)
    (hv : R.ωP i t (κ, κ') (R.vP i t) = c⁻¹ • R.vP i t)
    (hy : ∀ h, (R.HV i t).e y' h = c⁻¹ • (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)) :
    R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  have hpt : ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = c⁻¹ • R.ptP i t P :=
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t)
      κ hκ.1 κ' hκ' c⁻¹ hv
  have hker := fun P => GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hR.thP.ωP i t)
    (R.ptP i t P) (hR.thP.pt_theta i t P)
  have hm := thetaLift_shift hPF.1 (GQ (Vc D i)) κ κ' c hc0
    (integral_shift (Vc D i) (R.βV i) (R.datVt i t) g0 κ hκ (R.νV i t) (hR.models.νV i t).1.1 (R.fdV i t)
      (hR.models.νV i t).2)
    (fun P γ hγ g h => by
      have := (hker P).1 γ hγ 1 (GQ (Wc D i)).one_mem h g
      rwa [one_mul] at this)
    (fun P g h => (hker P).2 κ κ' c⁻¹ (hpt P) h g)
    ((R.extV i t).rangeRestrict y) ((R.extV i t).rangeRestrict y')
    (extV_left R hR.models.HV i t y)
    (fun h => (congrFun ((R.extV i t).map_smul c y').symm h).trans
      (extV_shift R hR.models.cV i t κ hκ.1 c hc0 y y' hy h))
    (PiTensorProduct.tprod ℂ v) x
  exact (congrFun (hPF.2 y' v) x).trans (hm.trans (congrFun (hPF.2 y v) (x * κ')).symm)

theorem thG_of_value_core (R : RealDat D A Ks) (F : Face D A) (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) (g : G)
    (y y' : (R.HV i t).H) (v : (R.MW i (sg0 D A)).Vec) (hv : ∀ τ, ‖(v τ : (R.MW i (sg0 D A)).H τ)‖ = 1)
    (hact : R.thF i t y' v = actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y v)) :
    R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  have hinj := GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i (sg0 D A)) (R.HW i (sg0 D A)).H (R.HW i (sg0 D A)).e _
    (R.νW i) (R.fdW i) (hR.models.HW i (sg0 D A)).2.2 v hv
  have e1 : (R.HW i (sg0 D A)).e (R.thG i t y') v = R.eWf i (sg0 D A) (R.thF i t y' v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.thP.thG i t y')
  have e2 : (R.HW i (sg0 D A)).e (R.thG i t y) v = R.eWf i (sg0 D A) (R.thF i t y v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.thP.thG i t y)
  have e3 : (R.HW i (sg0 D A)).e (R.gW i (sg0 D A) g (R.thG i t y)) v =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i (sg0 D A)).e (R.thG i t y) v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.models.gW i (sg0 D A) g (R.thG i t y))
  have e4 := (GlobalTheory.ProjComm.proj_comm R hR.lev hR.grp.record).2 i (sg0 D A) g _ (thF_type R hR.thP.thF_mem i t y v)
  exact hinj (e1.trans ((congrArg (R.eWf i (sg0 D A)) hact).trans (e4.trans
    ((congrArg (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) e2.symm).trans e3.symm))))

theorem thG_intertwines_core : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i t g κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ → ∀ y y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) → R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t g κ hκ y y' hy
  refine (Classical.em (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ')).elim
    (fun hl => hl.elim fun κ' hκ' => (hR.thP.ioP i t).2.2.elim fun v hv => hv.elim fun _ hw => ?_)
    (fun hl => (eq_zero_of_no_lift R hR.models.HW hR.models.gW i (sg0 D A) g hl _).trans
      (eq_zero_of_no_lift R hR.models.HW hR.models.gW i (sg0 D A) g hl _).symm)
  exact thG_of_value_core R F hR i t g y y' (fun ρ => v ρ) hw.1 (funext fun x =>
    (thF_shift_core R F hR i t (R.eG g) κ κ' hκ hκ'.1 y y' (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)
      (levChi_ne_zero (V := Vc D i) (β := R.βV i) (flagL (R.datVt i t)) κ)
      (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hR.lev hR.models.inf hR.thP.ωP hR.thP.vP i t (R.eG g) κ κ' hκ hκ') hy v x).trans
    (finiteGroup_acts_by_lift_translation_principalType R i (R.eG g) κ' hκ' _ (thF_type R hR.thP.thF_mem i t y _) x).symm)

end GlobalTheory.ThetaProjEquiv

end
