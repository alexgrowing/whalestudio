import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLinearForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.L2.Theta
open Formalism.BasicNotions.TH GlobalTheory.ThetaTri
open scoped Topology

section Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {M : MtFam D}

def fFin (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) :
    Bridge.Gf (Vc D i) → (R.cV i).W :=
  fun k => Ad.eW D.what₂.mu0 (reference_tuple_used D) i
    ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))

theorem fV_eq_ext (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) :
    fV Ad i Fm = (R.cV i).ext (fFin Ad i Fm) := rfl

theorem fFin_rat (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    {γ : GA D (Vc D i)} (hγ : γ ∈ GQ (Vc D i)) (k : Bridge.Gf (Vc D i)) :
    fFin Ad i Fm ((finHom (Vc D i)).rangeRestrict γ * k) = (R.cV i).ρ γ (fFin Ad i Fm k) := by
  set x := preF (Ad.PV i) ((finHom (Vc D i)).rangeRestrict γ) with hxdef
  have hx : finHom (Vc D i) γ = finHom (Vc D i) ((Ad.PV i).ψ x) :=
    (congrArg Subtype.val (GlobalTheory.ThetaFormV.fin_preF (Ad.PV i) ((finHom (Vc D i)).rangeRestrict γ))).symm
  have hrat : x ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := (Ad.rat i x).2 ⟨γ, hγ, hx⟩
  have e1 : preF (Ad.PV i) ((finHom (Vc D i)).rangeRestrict γ * k) = x * preF (Ad.PV i) k := by
    rw [GlobalTheory.ThetaFormV.preF_mul, ← hxdef]
  have hF := Fm.2.1 ⟨x, hrat⟩ (preF (Ad.PV i) k)
  unfold fFin
  rw [e1]
  rw [← Ad.wt D.what₂.mu0 (reference_tuple_used D) i ⟨x, hrat⟩ γ hγ hx]
  exact congrArg _ hF

theorem fV_invariant (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) :
    ∀ γ ∈ GQ (Vc D i), ∀ h, fV Ad i Fm (γ * h) = fV Ad i Fm h := by
  intro γ hγ h
  rw [fV_eq_ext, GlobalTheory.ThetaFormV.ext_apply, GlobalTheory.ThetaFormV.ext_apply, map_mul, fFin_rat Ad i Fm hγ]
  have e : (R.cV i).ρ (γ * h)⁻¹ * (R.cV i).ρ γ = (R.cV i).ρ h⁻¹ := by
    rw [← map_mul]; congr 1; group
  exact congrArg (fun T : Module.End ℂ (R.cV i).W => T _) e

end Forms

end GlobalTheory.RefTheta

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.L2.Theta
open Formalism.BasicNotions.TH GlobalTheory.ThetaTri Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Topology

section Cont

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {M : MtFam D}

theorem fV_continuous (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m)
    (hρ : ∀ x, Continuous fun g => (R.cV i).ρ g x)
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) :
    Continuous (fV Ad i Fm) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D (Vc D i)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
  obtain ⟨N, hN, hlev⟩ := Fm.2.2
  let J : Subgroup (Bridge.Gf (Vc D i)) :=
    { carrier := {q | ∀ k, fFin Ad i Fm (k * q) = fFin Ad i Fm k}
      mul_mem' := fun {a b} ha hb k => by simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [← mul_assoc, hb, ha]
      one_mem' := fun k => by rw [mul_one]
      inv_mem' := fun {a} ha k => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (k * a⁻¹), inv_mul_cancel_right] }
  have hfJ : fFin Ad i Fm ∈ Bridge.AdForms ((finHom (Vc D i)).rangeRestrict.comp (GQ (Vc D i)).subtype)
      ((R.cV i).ρ.comp (GQ (Vc D i)).subtype) J 1 :=
    GlobalTheory.ThetaFormV.mem_adForms_one _ _ (fun γ hγ k => fFin_rat Ad i Fm hγ k) J (fun q hq => hq)
  have hJ : ∀ᶠ κ in 𝓝 (1 : GA D (Vc D i)), ∃ h : (finHom (Vc D i)).rangeRestrict κ ∈ J,
      (1 : J →* ℂˣ) ⟨_, h⟩ = 1 := by
    filter_upwards [GlobalTheory.ThetaFormV.eventually_cong_preF (Ad.PV i) Y.hF
      ((GlobalTheory.HeightCounting.Up.StandardFrameAgreement.stdFrame_iff _ _).1 (Ad.std i)) hN] with κ hκ
    refine ⟨fun k => ?_, rfl⟩
    show fFin Ad i Fm (k * (finHom (Vc D i)).rangeRestrict κ) = fFin Ad i Fm k
    unfold fFin
    rw [GlobalTheory.ThetaFormV.preF_mul, hlev _ hκ]
  exact (GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D i)).rangeRestrict (GQ (Vc D i)) (R.cV i).ρ
    hρ hJ hfJ).congr fun g => (GlobalTheory.ThetaFormV.ext_apply _ _ _).symm

end Cont

end GlobalTheory.RefTheta

noncomputable section

namespace GlobalTheory.RefTheta

open scoped ComplexOrder

open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.ThetaTri in

theorem mem_Om_of_theta : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO R.ψ (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) (φ v)) → φ ∈ GlobalTheory.RefTheta.Om Ad i hc := by
  intro _ hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins _ hEx M Ad i X hc φ hφ
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hPins.char hEx).1
  have hm := core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := core.thP.ωP i (t0 Y)
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hHV := (hm.νV i (t0 Y)).1.1
  have hfdV := (hm.νV i (t0 Y)).2
  have hHW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hm.νW i).2
  have hρ : ∀ x, Continuous fun g => (R.cV i).ρ g x := (hm.cV i).2.2.1
  intro p
  have hφ' : ∀ v, IsThetaFunO R.ψ (Vc D i) (Wc D i) (valAct1 (omStd Ad i (t0 Y)) p φ v) :=
    fun v => hω.om_pres _ _ (hφ v)
  refine ⟨hφ', fun Fm g => ?_, fun Fm y => ?_⟩
  · have hc1 := fV_continuous Ad i hρ Fm
    have hc2 := fV_invariant Ad i Fm
    exact GlobalTheory.DefiniteQuotient.integrableOn_theta D R.ψ hω.std (Vc D i) (Wc D i) _ _ _ hω hpd _
      (valAct1 (omStd Ad i (t0 Y)) p φ) hφ' _ hc1 hc2 _ _ hHV hfdV g
  · have hc1 := fV_continuous Ad i hρ Fm
    have hc2 := fV_invariant Ad i Fm
    have hmap := (Classical.choose_spec (Classical.choose_spec hc)).2.2.1
    have hey : eC hc (y : X.A) ∈ Formalism.IndefR.principalLevelFrame.Minf R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) := by
      rw [← hmap]; exact ⟨y, y.2, rfl⟩
    have hyv : yv hc y = eC hc (y : X.A) (fun τ => ((Classical.epsilon fun u : ↥(lowT (R.MW i (sg0 D A3.A)) τ) =>
        ‖((u : (R.MW i (sg0 D A3.A)).sm τ) : (R.MW i (sg0 D A3.A)).H τ)‖ = 1 : ↥(lowT (R.MW i (sg0 D A3.A)) τ)) :
          (R.MW i (sg0 D A3.A)).sm τ)) := by
      simp [yv, kUnit, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
    obtain ⟨haut, hcu⟩ := GlobalTheory.T.multiplicitySpaceAllLevels_values_smooth_cuspidal R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) _ hey
      (fun τ => ((Classical.epsilon fun u : ↥(lowT (R.MW i (sg0 D A3.A)) τ) =>
        ‖((u : (R.MW i (sg0 D A3.A)).sm τ) : (R.MW i (sg0 D A3.A)).H τ)‖ = 1 : ↥(lowT (R.MW i (sg0 D A3.A)) τ)) :
          (R.MW i (sg0 D A3.A)).sm τ))
    rw [← hyv] at haut hcu
    have hR := (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ haut hcu).conj
    have hgr := GlobalTheory.T.moderateGrowth_definiteThetaIntegral_vectorForm R.ψ (Vc D i) (Wc D i) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (omStd Ad i (t0 Y)) p φ) hφ' _ hc1 hc2
    have hct := GlobalTheory.T.continuous_definiteThetaIntegral_vectorForm R.ψ (Vc D i) (Wc D i) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (omStd Ad i (t0 Y)) p φ) hφ' _ hc1 hc2
    have hinv : ∀ γ ∈ GQ (Wc D i), ∀ g, (∫ h in R.fdV i (t0 Y),
        thetaKO (R.ωP i (t0 Y)) h (γ * g)
          (valAct1 (omStd Ad i (t0 Y)) p φ (fV Ad i Fm h)) ∂(R.νV i (t0 Y))) =
        ∫ h in R.fdV i (t0 Y), thetaKO (R.ωP i (t0 Y)) h g
          (valAct1 (omStd Ad i (t0 Y)) p φ (fV Ad i Fm h)) ∂(R.νV i (t0 Y)) := by
      intro γ hγ g
      congr 1
      funext h
      have e : ((h, γ * g) : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hφ' _))
    have := hR.integrableOn_modGrowth_mul hHW hfdW hgr hinv hct.aestronglyMeasurable
    convert this using 1
    funext g
    simp only [Pi.mul_apply, thIn]
    rw [mul_comm]
    rfl

end GlobalTheory.RefTheta
