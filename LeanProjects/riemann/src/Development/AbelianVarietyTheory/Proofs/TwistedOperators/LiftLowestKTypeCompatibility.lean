import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvalInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightOfMemCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eq_zero_of_no_lift (R : RealDat D A Ks) (hW : R.models_HW) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g : G) (hn : ¬ ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ) (x : (R.HW i σ).H) : x = 0 := by
  have hL : actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) = 0 := by
    ext F h
    show actG0 _ _ _ _ F h = 0
    rw [GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hn F]
    rfl
  have h1 : (R.HW i σ).e (R.gW i σ g x) = 0 := by
    rw [hg i σ g x, hL]
    ext v h
    rfl
  have h2 : R.gW i σ g x = 0 := (hW i σ).1 (by rw [h1, map_zero])
  have h3 := congrArg (R.gW i σ g⁻¹) h2
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at h3

theorem realDatum_coeffFlagLevelCharacter_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  classical
  unfold levChi Formalism.L2.DIV.levFn
  simp [flagL, withP, LevCh.datWp, datY, Formalism.L2.DIV.ext1, Formalism.L2.DIV.LevelP.full]
  exact dite_eq_right_iff.mpr fun _ => rfl

theorem left_abs {H Gf W : Type} [Group H] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Γ : Subgroup H)
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (f : Gf → W) (J : Subgroup Gf) (χ : J →* ℂˣ)
    (hy : f ∈ Bridge.AdForms (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) (γ : H) (hγ : γ ∈ Γ) (h : H) :
    ρ (γ * h)⁻¹ (f (p (γ * h))) = ρ h⁻¹ (f (p h)) := by
  have h1 : f (p γ * p h) = ρ γ (f (p h)) := by
    have h0 : f (p γ * p h * 1) = ((χ 1 : ℂˣ) : ℂ) • ρ γ (f (p h)) := hy ⟨γ, hγ⟩ (p h) 1
    simpa using h0
  rw [map_mul p, h1, mul_inv_rev, map_mul ρ, Module.End.mul_apply, ← Module.End.mul_apply (ρ γ⁻¹), ← map_mul ρ,
    inv_mul_cancel, map_one, Module.End.one_apply]

theorem shift_abs {H Gf W : Type} [Group H] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (κ : H) (hκ : ρ κ⁻¹ = 1) (a : ℂ) (ha : a ≠ 0) (f f' : Gf → W)
    (hy : ∀ h, f' h = a⁻¹ • f (h * p κ)) (h : H) :
    ρ h⁻¹ ((a • f') (p h)) = ρ (h * κ)⁻¹ (f (p (h * κ))) := by
  rw [Pi.smul_apply, hy, smul_smul, mul_inv_cancel₀ ha, one_smul, map_mul p, mul_inv_rev, map_mul ρ,
    Module.End.mul_apply, hκ, Module.End.one_apply]

theorem ext_left {V : HSp D} (c : CoefA V) (f : Bridge.Gf V → c.W) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ)
    (hy : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) J χ)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : c.ext f (γ * h) = c.ext f h := by
  show c.ρ (γ * h)⁻¹ (f ((finHom V).rangeRestrict (γ * h))) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h))
  exact left_abs (GQ V) (finHom V).rangeRestrict c.ρ f J χ hy γ hγ h

theorem ext_shift {V : HSp D} (c : CoefA V) (hc : c.Is) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (h : GA D V) :
    c.ext (a • f') h = c.ext f (h * κ) := by
  show c.ρ h⁻¹ ((a • f') ((finHom V).rangeRestrict h)) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ)))
  exact shift_abs (finHom V).rangeRestrict c.ρ κ (hc.1 _ (inv_mem hκ)) a ha f f' hy h

theorem extV_left (R : RealDat D A Ks) (hV : R.models_HV) (i : Fin D.R.m) (t : T0) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) : R.extV i t y (γ * h) = R.extV i t y h := by
  have h3 := LinearMap.mem_range_self (R.HV i t).e y
  rw [(hV i t).2.1] at h3
  show (R.cV i).ext ((R.HV i t).e y) (γ * h) = (R.cV i).ext ((R.HV i t).e y) h
  exact ext_left (R.cV i) _ _ _ h3 γ hγ h

theorem extV_shift (R : RealDat D A Ks) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (κ : GA D (Vc D i))
    (hκ : κ ∈ GfC (Vc D i)) (c : ℂ) (hc0 : c ≠ 0) (y y' : (R.HV i t).H)
    (hy : ∀ h, (R.HV i t).e y' h = c⁻¹ • (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ)) (h : GA D (Vc D i)) :
    R.extV i t (c • y') h = R.extV i t y (h * κ) := by
  show (R.cV i).ext ((R.HV i t).e (c • y')) h = (R.cV i).ext ((R.HV i t).e y) (h * κ)
  rw [map_smul]
  exact ext_shift (R.cV i) (hc i) κ hκ c hc0 _ _ hy h

theorem integral_shift (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r)
    (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) 𝓕 ν) (f : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h)
    (hi : IntegrableOn f 𝓕 ν) : ∫ h in 𝓕, f (h * κ) ∂ν = ∫ h in 𝓕, f h ∂ν := by
  obtain ⟨htg, hlc, hsc, -, hbo, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨-, -, -, hct⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  obtain ⟨hK, hlift⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
  haveI := htg
  haveI := hlc
  haveI := hsc
  haveI := hbo
  haveI := hct
  haveI := hν
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup ν _ hK κ (hlift g0 κ hκ)
  exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) ν 𝓕 hfd κ hmap f hf hi).2

theorem thetaLift_shift {G' H' S' Sinf TK Tau : Type} [Group G'] [Group H'] [MeasurableSpace H']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Sinf → S'} {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf}
    {B : Submodule ℂ (H' → Tau)} {thP : B →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))} (hP : Lift.IsThetaP ν 𝓕 th pt io B thP)
    (Γ : Subgroup H') (k : H') (k' : G') (c : ℂ) (hc : c ≠ 0)
    (hsh : ∀ f : H' → ℂ, (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) → IntegrableOn f 𝓕 ν →
      ∫ h in 𝓕, f (h * k) ∂ν = ∫ h in 𝓕, f h ∂ν)
    (hl : ∀ P, ∀ γ ∈ Γ, ∀ g h, th g (γ * h) (pt P) = th g h (pt P))
    (hr : ∀ P g h, th (g * k') (h * k) (pt P) = c⁻¹ * th g h (pt P))
    (f f' : B) (hf : ∀ γ ∈ Γ, ∀ h, (f : H' → Tau) (γ * h) = (f : H' → Tau) h)
    (hf' : ∀ h, ((c • f' : B) : H' → Tau) h = (f : H' → Tau) (h * k)) (e : TK) (g : G') :
    thP f' e g = thP f e (g * k') := by
  have hA : thP f e (g * k') = ∫ h in 𝓕, th (g * k') h (pt (io e ((f : H' → Tau) h))) ∂ν :=
    hP.eq f e (g * k')
  have hB : thP (c • f') e g = ∫ h in 𝓕, th g h (pt (io e (((c • f' : B) : H' → Tau) h))) ∂ν :=
    hP.eq (c • f') e g
  have hF := hsh (fun h => th (g * k') h (pt (io e ((f : H' → Tau) h))))
    (fun γ hγ h => by
      rw [hf γ hγ h]
      exact hl _ γ hγ _ _)
    (hP.integ f e (g * k'))
  rw [hA, ← hF]
  simp only [hr]
  rw [integral_const_mul]
  have hfk : ∀ h, (f : H' → Tau) (h * k) = ((c • f' : B) : H' → Tau) h := fun h => (hf' h).symm
  simp only [hfk]
  rw [← hB, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem thF_type (R : RealDat D A Ks) (hm : R.thP_thF_mem) (i : Fin D.R.m) (t : T0) (y : (R.HV i t).H)
    (v : (R.MW i (sg0 D A)).Vec) : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (R.thF i t y v) := by
  intro κ hκ h
  have hmem : R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) := hm i t y
  exact (GlobalTheory.mult_value_left_cont_level R.θ _ _ _ _ hmem v).2.2 κ hκ h

theorem finiteGroup_acts_by_lift_translation_principalType (R : RealDat D A Ks) (i : Fin D.R.m) (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i))
    (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (f : GA D (Wc D i) → ℂ)
    (hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) f) (x : GA D (Wc D i)) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 f x = f (x * κ') := by
  have hex : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ := ⟨κ', hκ'⟩
  have hchi : ∀ k, levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
    intro k
    classical
    unfold levChi Formalism.L2.DIV.levFn
    simp [LevCh.datWp, datY, Formalism.L2.DIV.ext1, Formalism.L2.DIV.LevelP.triv]
    exact dite_eq_right_iff.mpr fun _ => rfl
  have hmem := lift_div_mem hκ' hex.choose_spec
  have hfl : flag1L (R.datWp i R.triv) = R.datWp i R.triv := rfl
  rw [hfl] at hmem
  have hx := hT _ hmem (x * κ')
  rw [hchi, one_mul, ← mul_assoc, mul_inv_cancel_right] at hx
  show actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) g0 f x = f (x * κ')
  unfold actG0
  rw [dif_pos hex, realDatum_coeffFlagLevelCharacter_eq_one, inv_one, one_mul]
  exact hx

end GlobalTheory.ThetaProjEquiv

end
