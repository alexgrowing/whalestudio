import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrandStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem representation_inv_mul_apply_cancel_left {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H)
    (v : W) : ρ (γ * h)⁻¹ (ρ γ v) = ρ h⁻¹ v := by
  rw [← Module.End.mul_apply, ← map_mul]; congr 2; group

theorem representation_inv_mul_smul_one_of_trivial_right {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (h κ : H)
    (hκ : ρ κ⁻¹ = 1) (c : ℂ) (v : W) : ρ (h * κ)⁻¹ (c • ρ 1 v) = c • ρ h⁻¹ v := by
  rw [map_one, Module.End.one_apply, map_smul, _root_.mul_inv_rev, map_mul, hκ, one_mul]

theorem extV_law (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) :
    (R.HV i t).e y (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x * k) =
      ((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ) • (R.cV i).ρ γ ((R.HV i t).e y x) := by
  have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ _
  exact (SetLike.ext_iff.mp (hM.HV i t).2.1 ((R.HV i t).e y)).mp h1 γ x k

theorem extV_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (γ * h) = R.extV i t y h := by
  have hx : (finHom (Vc D i)).rangeRestrict (γ * h) = Formalism.IndefR.Bridge.ratF (Vc D i) ⟨γ, hγ⟩ *
      (finHom (Vc D i)).rangeRestrict h * ((1 : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [Formalism.IndefR.Bridge.ratF]
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h)) = (R.cV i).ρ γ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y ⟨γ, hγ⟩ ((finHom (Vc D i)).rangeRestrict h) 1
      _ = _ := by simp only [map_one, Units.val_one, one_smul]
  show (R.cV i).ρ (γ * h)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h))) =
    (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_apply_cancel_left _ γ h _

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (κ : GA D (Vc D i)) (hκ : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t))) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • R.extV i t y h := by
  let k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J := ⟨(finHom (Vc D i)).rangeRestrict κ, hκ.2⟩
  have hx : (finHom (Vc D i)).rangeRestrict (h * κ) = Formalism.IndefR.Bridge.ratF (Vc D i) 1 *
      (finHom (Vc D i)).rangeRestrict h * (k : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [k]
  have hχ : (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ := rfl
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ)) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • (R.cV i).ρ 1 ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y 1 ((finHom (Vc D i)).rangeRestrict h) k
      _ = _ := congrArg (· • _) hχ
  show (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ))) =
    _ • (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_smul_one_of_trivial_right _ h κ ((hM.cV i).1 _ ((GfC (Vc D i)).inv_mem hκ.1)) _ _

def compF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ) :
    GA D (Vc D i) → ℂ :=
  fun h => l (R.extV i t y h)

theorem compF_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (compF R i t y l) := by
  intro k hk h
  exact (congrArg l (extV_type R hM i t y k hk h)).trans (by rw [map_smul, smul_eq_mul]; rfl)

theorem compF_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    compF R i t y l (γ * h) = compF R i t y l h :=
  congrArg l (extV_left R hM i t y γ hγ h)

theorem theta_left (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hP : R.FullP)
    (φ : WO (Vc D i) (Wc D i) → ℂ) (hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ) (g : GA D (Wc D i))
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) (γ * h) g φ = thetaKO (R.ωP i t) h g φ := by
  have hm : ((γ * h, g) : GA D (Vc D i) × GA D (Wc D i)) = (γ, 1) * (h, g) := by rw [Prod.mk_mul_mk, one_mul]
  show R.ωP i t (γ * h, g) φ 0 = R.ωP i t (h, g) φ 0
  rw [hm, map_mul, Module.End.mul_apply]
  exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ φ hφ)

theorem theta_transl (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (φ : WO (Vc D i) (Wc D i) → ℂ)
    (g : GA D (Wc D i)) (κ h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) φ) = thetaKO (R.ωP i t) (h * κ) g φ := by
  show R.ωP i t (h, g) (R.ωP i t (κ, 1) φ) 0 = R.ωP i t (h * κ, g) φ 0
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem theta_avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        thetaKO (R.ωP i t) (h * (κ j)⁻¹) g f := by
  rw [← Finset.sum_congr rfl fun j _ => congrArg (_ * ·) (theta_transl R i t f g (κ j)⁻¹ h)]
  show R.ωP i t (h, g) (avgW R i t PP a tr ε κ f) 0 = _
  simp only [avgW, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem sum_compF_eq_zero (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (hNC : NoChi R i t y) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (ha : a ≠ 0) (tr : Bool) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (κ : G → GA D (Vc D i)) (hκ : IsLifts R i t κ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (h : GA D (Vc D i)) :
    ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      compF R i t y l (h * κ j) = 0 := by
  have h0 := congrFun (hNC PP a ha tr ε hε l) h
  refine Eq.trans ?_ h0
  simp only [gaL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = mirC R i PP a tr ε j * actG0 (Vc D i) (R.βV i) (R.datVt i t) (R.eG j) (compF R i t y l) h
  rw [level_action_spec (compF_type R hM i t y l) ⟨κ j, hκ j⟩ (κ j) (hκ j) h]
  ring

def termF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) : GA D (Vc D i) → ℂ :=
  fun h => thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h

theorem termF_eq (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) :
    (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ⁻¹, 1) f) * l (R.extV i t y h)) = termF R i t y l f g κ := by
  funext h
  exact congrArg (· * l (R.extV i t y h)) (theta_transl R i t f g κ⁻¹ h)

theorem termF_left (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.FullP) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f)
    (g : GA D (Wc D i)) (κ : GA D (Vc D i)) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    termF R i t y l f g κ (γ * h) = termF R i t y l f g κ h := by
  show thetaKO (R.ωP i t) (γ * h * κ⁻¹) g f * compF R i t y l (γ * h) =
    thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h
  rw [mul_assoc, theta_left R i t hP f hf g γ hγ, compF_left R hM i t y l γ hγ h]

theorem avgLaw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hNC PP a ha tr ε hε κ hκ f hf l g
  have hM := hG.core.models
  obtain ⟨hmeas, hfd⟩ := hM.νV i t
  haveI : (R.νV i t).IsHaarMeasure := hmeas.1
  haveI : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hmeas.1
  have hu_int : ∀ j, IntegrableOn (termF R i t y l f g (κ j)) (R.fdV i t) (R.νV i t) := by
    intro j
    have h1 := GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y (R.ωP i t ((κ j)⁻¹, 1) f) l g
      ((hP i t).datum.om_pres _ f hf)
    exact (congrArg (fun φ => IntegrableOn φ (R.fdV i t) (R.νV i t)) (termF_eq R i t y l f g (κ j))).mp h1
  have hv_int : ∀ j, IntegrableOn (fun h => termF R i t y l f g (κ j) (h * κ j)) (R.fdV i t) (R.νV i t) :=
    fun j => GlobalTheory.integrableOn_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h) (hu_int j)
  have hsub : ∀ j, ∫ h in R.fdV i t, termF R i t y l f g (κ j) h ∂(R.νV i t) =
      ∫ h in R.fdV i t, termF R i t y l f g (κ j) (h * κ j) ∂(R.νV i t) :=
    fun j => (GlobalTheory.setIntegral_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h)).symm
  have hpt1 : ∀ h, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        termF R i t y l f g (κ j) h := by
    intro h
    rw [theta_avgW, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  have hpt2 : ∀ h, ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      termF R i t y l f g (κ j) (h * κ j) = 0 := by
    intro h
    have e : ∀ j, termF R i t y l f g (κ j) (h * κ j) = thetaKO (R.ωP i t) h g f * compF R i t y l (h * κ j) := by
      intro j
      show thetaKO (R.ωP i t) (h * κ j * (κ j)⁻¹) g f * _ = _
      rw [mul_inv_cancel_right]
    simp only [e]
    rw [← mul_zero (thetaKO (R.ωP i t) h g f), ← sum_compF_eq_zero R hM i t y hNC PP a ha tr ε hε κ hκ l h,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h ∂(R.νV i t) = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt1),
    integral_finset_sum _ fun j _ => (hu_int j).const_mul _]
  simp only [integral_const_mul]
  simp only [hsub]
  simp only [← integral_const_mul]
  rw [← integral_finset_sum _ fun j _ => (hv_int j).const_mul _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt2)]
  exact integral_zero _ _

end GlobalTheory.DownLift.GenFinite

end
