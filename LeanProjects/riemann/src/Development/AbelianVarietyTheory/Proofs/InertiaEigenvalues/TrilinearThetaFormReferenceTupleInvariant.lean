import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftEquivariance
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section
namespace GlobalTheory.RefTheta
open scoped TensorProduct
open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame GlobalTheory.ThetaTri GlobalTheory.ThetaLoc

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {M : MtFam D}

theorem fV_rt (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (hcv : (R.cV i).Is) (h : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (Fm Fm' : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    (hF : (Fm' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = NG.rt D.host.E D.R.nV h Fm)
    (x : Formalism.L2.Theta.GA D (Vc D i)) : RefTheta.fV Ad i Fm' x = RefTheta.fV Ad i Fm (x * (Ad.PV i).ψ h) := by
  show (R.cV i).ext _ x = (R.cV i).ext _ (x * (Ad.PV i).ψ h)
  rw [GlobalTheory.DefLiftHecke.ext_mul _ hcv _ ((Ad.PV i).into h) x]
  show (R.cV i).ρ x⁻¹ _ = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk, preF_mul, hF, NG.rt]

theorem fV_rat (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    (γ : Formalism.L2.Theta.GA D (Vc D i)) (hγ : γ ∈ Formalism.L2.Theta.GQ (Vc D i)) (x : Formalism.L2.Theta.GA D (Vc D i)) :
    RefTheta.fV Ad i Fm (γ * x) = RefTheta.fV Ad i Fm x := by
  obtain ⟨y, hy⟩ := fin_frame_surj (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict γ)
  obtain ⟨z, hz⟩ := fin_frame_surj (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict x)
  have he : Formalism.L2.Theta.finHom (Vc D i) γ = Formalism.L2.Theta.finHom (Vc D i) ((Ad.PV i).ψ y) :=
    (congrArg Subtype.val hy).symm
  have hh' : y ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := (Ad.rat i _).2 ⟨γ, hγ, he⟩
  show (R.cV i).ρ (γ * x)⁻¹ (Ad.eW D.what₂.mu0 (reference_tuple_used D) i ((Fm : Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W)
      (preF (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict (γ * x))))) =
    (R.cV i).ρ x⁻¹ (Ad.eW D.what₂.mu0 (reference_tuple_used D) i ((Fm : Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W)
      (preF (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict x))))
  have hprod : (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict γ * (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict x =
      (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict ((Ad.PV i).ψ (y * z)) :=
    (congrArg₂ (· * ·) hy.symm hz.symm).trans
      ((map_mul (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict _ _).symm.trans
        (congrArg (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict (map_mul (Ad.PV i).ψ y z).symm))
  have key : preF (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict (γ * x)) = y * z :=
    (congrArg (preF (Ad.PV i)) ((map_mul (Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict γ x).trans hprod)).trans (preF_frame _ _)
  have hz' : preF (Ad.PV i) ((Formalism.L2.Theta.finHom (Vc D i)).rangeRestrict x) = z :=
    (congrArg (preF (Ad.PV i)) hz.symm).trans (preF_frame _ _)
  rw [key, hz']
  have e1 := Fm.2.1 ⟨y, hh'⟩ z
  have e2 := Ad.wt D.what₂.mu0 (reference_tuple_used D) i ⟨y, hh'⟩ γ hγ he
    ((Fm : Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) z)
  rw [e1, e2, _root_.mul_inv_rev,
    map_mul, Module.End.mul_apply, ← Module.End.mul_apply ((R.cV i).ρ γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem yv_apply {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) (y : ↥X.C) (x : Formalism.L2.Theta.GA D (Wc D i)) :
    RefTheta.yv hc y x = PiTensorProduct.lift (RefTheta.eC hc (y : X.A)) (PiTensorProduct.map
      (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype) (kUnit (R.MW i (sg0 D A3.A)))) x := rfl

theorem yv_rt {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X)
    (g : Formalism.AUTREP.GAf D.host.E D.R.r) (y y' : ↥X.C) (hy : (y' : X.A) = X.ρ g y) (x : Formalism.L2.Theta.GA D (Wc D i)) :
    RefTheta.yv hc y' x = RefTheta.yv hc y (x * (Y.PW i).ψ g) := by
  have he : RefTheta.eC hc (y' : X.A) = Formalism.IndefR.principalLevelFrame.actM (Y.PW i) (R.MW i (sg0 D A3.A)) g (RefTheta.eC hc (y : X.A)) := by
    rw [hy]; exact (Classical.choose_spec (Classical.choose_spec hc)).2.2.2.1 g y
  rw [RefTheta.yv_apply, RefTheta.yv_apply, he, lift_actM]

theorem yv_rat {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X)
    (y : ↥X.C) (γ : Formalism.L2.Theta.GA D (Wc D i)) (hγ : γ ∈ Formalism.L2.Theta.GQ (Wc D i)) (x : Formalism.L2.Theta.GA D (Wc D i)) :
    RefTheta.yv hc y (γ * x) = RefTheta.yv hc y x := by
  have hm : RefTheta.eC hc (y : X.A) ∈ LeftInvM (R.MW i (sg0 D A3.A)) := by
    apply minf_le_leftInv R.θ (Y.PW i)
    rw [← (Classical.choose_spec (Classical.choose_spec hc)).2.2.1]
    exact Submodule.mem_map_of_mem y.2
  rw [RefTheta.yv_apply, RefTheta.yv_apply]
  exact lift_left _ _ hm _ γ hγ x

theorem lamV_inv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), φ ∈ GlobalTheory.RefTheta.Om Ad i hc → ∀ (Fm Fm' : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y y' : ↥X.C), (Fm' : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = NG.rt D.host.E D.R.nV h Fm → (y' : X.A) = X.ρ g y → GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.ThetaTri.valAct1 (GlobalTheory.RefTheta.omStd Ad i (GlobalTheory.RefTheta.t0 Y)) (h, g) φ) Fm' y' = GlobalTheory.RefTheta.lamV Ad i hc φ Fm y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i X hc h g φ hφ Fm Fm' y y' hF hy
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hW := hcore.thP.ωP i (t0 Y)
  have hcv : (R.cV i).Is := hcore.models.cV i
  have hth : ∀ v, IsThetaFunO R.ψ (Vc D i) (Wc D i) (φ v) := by
    intro v
    have := (hφ 1).1 v
    simpa [valAct1_apply] using this
  have hV := hcore.models.νV i (t0 Y)
  have hWm := hcore.models.νW i
  haveI : (R.νV i (t0 Y)).IsHaarMeasure := hV.1.1
  haveI : (R.νV i (t0 Y)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hV.1.1
  haveI : (R.νW i).IsHaarMeasure := hWm.1.1
  haveI : (R.νW i).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hWm.1.1
  haveI : Countable (Formalism.L2.Theta.GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Vc D i).gram
  haveI : Countable (Formalism.L2.Theta.GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Wc D i).gram
  have inner : ∀ g₀, thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i) (R.νV i (t0 Y))
      (R.fdV i (t0 Y)) (valAct1 (RefTheta.omStd Ad i (t0 Y)) (h, g) φ) Fm' g₀ =
      thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i) (R.νV i (t0 Y))
      (R.fdV i (t0 Y)) φ Fm (g₀ * (Y.PW i).ψ g) := by
    intro g₀
    unfold thIn
    have e1 : ∀ h₀, thetaKO (R.ωP i (t0 Y)) h₀ g₀
        (valAct1 (RefTheta.omStd Ad i (t0 Y)) (h, g) φ (RefTheta.fV Ad i Fm' h₀)) =
        thetaKO (R.ωP i (t0 Y)) (h₀ * (Ad.PV i).ψ h) (g₀ * (Y.PW i).ψ g)
          (φ (RefTheta.fV Ad i Fm (h₀ * (Ad.PV i).ψ h))) := by
      intro h₀
      rw [valAct1_apply, RefTheta.fV_rt Ad i hcv h Fm Fm' hF h₀]
      exact thetaKO_act _ _ _ _ _
    simp only [e1]
    refine (Formalism.IndefR.Eqv.rightInv_holds _ (Formalism.L2.Theta.GQ (Vc D i)) _ _ hV.2
      (fun h₁ => thetaKO (R.ωP i (t0 Y)) h₁ (g₀ * (Y.PW i).ψ g) (φ (RefTheta.fV Ad i Fm h₁))) ?_ _).2
    intro γ hγ h₁
    rw [RefTheta.fV_rat Ad i Fm γ hγ h₁]
    have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (RefTheta.fV Ad i Fm h₁))).1 γ hγ 1
      (one_mem _) h₁ (g₀ * (Y.PW i).ψ g)
    rwa [one_mul] at this
  unfold GlobalTheory.RefTheta.lamV GlobalTheory.ThetaTri.lamV
  congr 1
  have e2 : ∀ g₀, star (RefTheta.yv hc y' g₀) * thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i)
      (R.νV i (t0 Y)) (R.fdV i (t0 Y))
      (valAct1 (RefTheta.omStd Ad i (t0 Y)) (h, g) φ) Fm' g₀ =
      star (RefTheta.yv hc y (g₀ * (Y.PW i).ψ g)) * thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i)
      (R.νV i (t0 Y)) (R.fdV i (t0 Y)) φ Fm (g₀ * (Y.PW i).ψ g) := by
    intro g₀
    rw [inner, RefTheta.yv_rt hc g y y' hy]
  simp only [e2]
  refine (Formalism.IndefR.Eqv.rightInv_holds _ (Formalism.L2.Theta.GQ (Wc D i)) _ _ hWm.2
    (fun g₁ => star (RefTheta.yv hc y g₁) * thIn (R.ωP i (t0 Y)) (RefTheta.fV Ad i)
      (R.νV i (t0 Y)) (R.fdV i (t0 Y)) φ Fm g₁) ?_ _).2
  intro γ hγ g₁
  rw [RefTheta.yv_rat hc y γ hγ g₁]
  congr 1
  unfold thIn
  congr 1
  funext h₁
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (RefTheta.fV Ad i Fm h₁))).1 1 (one_mem _) γ hγ
    h₁ g₁
  rwa [one_mul] at this

end GlobalTheory.RefTheta

end
