import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightOfMemCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7}

theorem setIntegral_mul_right_of_fd {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  rw [h𝓕.setIntegral_eq h2 hinv]
  exact hmp.setIntegral_preimage_emb hemb f 𝓕

theorem flagOneLevel_eq_self_of_trivial {n : ℕ} (L : LevDat D.host.E ℂ n) (hL : L.P = LevelP.triv L.Pg L.r ℂ) : flag1L L = L := by
  cases L
  simp only at hL
  subst hL
  rfl

theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ) (x : G) (k : J) : F (x * k) = (χ k : ℂ) • F x := by
  have h1 := hF 1 x k
  rw [map_one, one_mul, map_one, Module.End.one_apply] at h1
  exact h1

theorem adForm_type (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V)
    (F : Formalism.IndefR.Bridge.Gf V → c.W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) (x : Formalism.IndefR.Bridge.Gf V) :
    F (x * (finHom V).rangeRestrict κ) = levChi V β (flag1L L) κ • F x := by
  have hmem : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J := by
    show finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)
    exact hκ.2
  have h1 := adForms_right (W := c.W) (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ F hF x ⟨_, hmem⟩
  have hχ : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = levChi V β (flag1L L) κ := rfl
  rw [hχ] at h1
  exact h1

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem datVt_P {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    (R.datVt i t).P = LevelP.triv (R.datVt i t).Pg (R.datVt i t).r ℂ := by
  simp [LevCh.datVt, datY, LevelP.conj, LevelP.triv]
  rfl

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (κ : GA D (Vc D i))
    (hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ • R.extV i t y h := by
  have hL : flag1L (R.datVt i t) = R.datVt i t := flagOneLevel_eq_self_of_trivial _ (datVt_P R i t)
  have hκ1 : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := by rw [hL]; exact hκ
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = levChi (Vc D i) (R.βV i) (R.datVt i t) κ := by rw [hL]
  have hyA : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le ⟨y, rfl⟩
  have hty : ∀ x, (R.HV i t).e y x = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ •
      (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) := by
    intro x
    have h1 := adForm_type (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) ((R.HV i t).e y) hyA κ hκ1 x
    have h2 : (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) =
        levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y x :=
      h1.trans (congrArg (· • (R.HV i t).e y x) hchi)
    exact (inv_smul_smul₀ hc0 _).symm.trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • ·) h2.symm)
  have e1 := GlobalTheory.ThetaProjEquiv.ext_shift (R.cV i) (hM.cV i) κ hκ.1 _ hc0 ((R.HV i t).e y) ((R.HV i t).e y) hty h
  have hx : ∀ z, R.extV i t y z = (R.cV i).ext ((R.HV i t).e y) z := fun z => rfl
  have e2 : (R.cV i).ext (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y) h =
      levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.cV i).ext ((R.HV i t).e y) h := by
    exact congrFun (LinearMap.map_smul (R.cV i).ext _ ((R.HV i t).e y)) h
  exact (hx (h * κ)).trans (e1.symm.trans (e2.trans (congrArg (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • ·) (hx h).symm)))

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem alg_step {a b c d d' : ℂ} (hc : c ≠ 0) (hab : a = b) (hd : d' = c * d) : a * d = c⁻¹ * (b * d') := by
  rw [hab, hd, mul_left_comm b c d, inv_mul_cancel_left₀ hc]

theorem downInt_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (κ, 1) f) l g = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * downInt R i t y f l g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f hf κ hκ l g
  have hM := hG.core.models
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hFn : ∀ h, l (R.extV i t y (h * κ)) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ * l (R.extV i t y h) := by
    intro h
    exact (congrArg l (extV_type R hM i t y κ hκ h)).trans (l.map_smul _ _)

  have hth : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) = thetaKO (R.ωP i t) (h * κ) g f := by
    intro h
    have hm : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) * (κ, 1) = (h * κ, g) := by
      rw [Prod.mk_mul_mk, mul_one]
    show R.ωP i t (h, g) (R.ωP i t (κ, 1) f) 0 = R.ωP i t (h * κ, g) f 0
    rw [← hm, map_mul, Module.End.mul_apply]

  let Φ : GA D (Vc D i) → ℂ := fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)
  have hΦ : ∀ γ ∈ GQ (Vc D i), ∀ h, Φ (γ * h) = Φ h := by
    intro γ hγ h
    have ht : thetaKO (R.ωP i t) (γ * h) g f = thetaKO (R.ωP i t) h g f := by
      have hm : ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (h, g) = (γ * h, g) := by
        rw [Prod.mk_mul_mk, one_mul]
      show R.ωP i t (γ * h, g) f 0 = R.ωP i t (h, g) f 0
      rw [← hm, map_mul, Module.End.mul_apply]
      exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ _ hf)
    have hl : l (R.extV i t y (γ * h)) = l (R.extV i t y h) :=
      congrArg l (GlobalTheory.ThetaProjEquiv.extV_left R hM.HV i t y γ hγ h)
    exact congrArg₂ (· * ·) ht hl

  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Vc D i)
  have : IsTopologicalGroup (GA D (Vc D i)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
  have hH : (R.νV i t).IsHaarMeasure := (hM.νV i t).1.1
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup (R.νV i t) _
    (GlobalTheory.ParahoricCompact.isCompact_levG (Vc D i) (R.βV i) (R.datVt i t)) κ hκ
  have hint := setIntegral_mul_right_of_fd (GQ (Vc D i)) (R.νV i t) (R.fdV i t) (hM.νV i t).2 κ hmap Φ hΦ
  have hfun : (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) * l (R.extV i t y h)) =
      fun h => (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * Φ (h * κ) := by
    funext h
    exact alg_step hc0 (hth h) (hFn h)
  exact (congrArg (fun φ : GA D (Vc D i) → ℂ => ∫ h in R.fdV i t, φ h ∂(R.νV i t)) hfun).trans
    ((integral_const_mul _ _).trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * ·) hint))

end GlobalTheory.DownLift.TypeLaw
