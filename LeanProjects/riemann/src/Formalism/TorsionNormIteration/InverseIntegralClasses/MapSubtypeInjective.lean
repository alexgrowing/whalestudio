import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.FormalGroupLog.LogDeterminesLaw

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.Asm

open Formalism.G

section Integral

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem integralMv_add {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a + b) := by
  intro d
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) (hb d))

theorem integralMv_sub {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by
  intro d
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) ?_)
  rw [norm_neg]
  exact hb d

theorem integralMv_X {ι : Type*} (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem funEqMv_add {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ (a + b) := by
  unfold IsFunEqTypeMv at *
  convert integralMv_add ha hb using 1
  simp only [map_add, smul_add]
  abel

theorem funEqMv_sub {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ (a - b) := by
  unfold IsFunEqTypeMv at *
  convert integralMv_sub ha hb using 1
  simp only [map_sub, smul_sub]
  abel

end Integral

theorem q_ne_zero {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : q ≠ 0 := by
  obtain ⟨hp, ⟨k, -, rfl⟩, -⟩ := h
  exact pow_ne_zero _ hp.ne_zero

theorem two_le_q {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : 2 ≤ q := by
  obtain ⟨hp, ⟨k, hk, rfl⟩, -⟩ := h
  exact hp.two_le.trans (Nat.le_self_pow (by omega) _)

theorem funEqInv (h2 : InvIntegralOfClass.{u, 0}) (h3 : FunEqLowCoeff.{u, 0})
    (hk : Formalism.G.FunEqSubst.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {p q : ℕ} {σ : K →+* K}
    (hS : FunctionalEquationSetting K p q σ) {ι : Type} [Finite ι] {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfE : IsFunEqType p q σ f)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hC : IsFunEqTypeMv p q (q_ne_zero hS) σ (f.subst h)) : IntegralMv h :=
  h2 K ι (IsFunEqTypeMv p q (q_ne_zero hS) σ) f hf0 hf1
    (fun _ _ ha hb => funEqMv_sub _ _ ha hb)
    (fun P hP0 hPI => hk K p q (q_ne_zero hS) σ hS f hf0 hfE ι P hP0 hPI)
    (fun D hD N hN hlow d hd => h3 K ι p q (q_ne_zero hS) σ (two_le_q hS) D hD N hN hlow d hd)
    h hh0 hC

theorem FunEqGroup_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfE
  have hq := q_ne_zero hS
  have hG0 : MvPowerSeries.constantCoeff (atX f + atY f) = 0 := by
    rw [map_add, atX, atY, PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0,
      PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0, add_zero]
  have hGE : IsFunEqTypeMv p q hq σ (atX f + atY f) :=
    funEqMv_add hq σ (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 0))
      (hk K p q hq σ hS f hf0 hfE (Fin 2) _ (by simp) (integralMv_X 1))
  obtain ⟨F, hF0, hF⟩ := h1 K (Fin 2) f (atX f + atY f) hf0 hf1 hG0
  refine ⟨F, hF0, funEqInv h2 h3 hk hS hf0 hf1 hfE F hF0 ?_, hF⟩
  rw [hF]
  exact hGE

theorem funEqType_unit {K : Type u} [NormedField K] {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K}
    {g : PowerSeries K} (hg : IsFunEqType p q σ g) :
    IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K) := by
  have hx : (PowerSeries.map σ g).subst ((PowerSeries.X : PowerSeries K) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro d
  have := hg (d ())
  rw [hx] at this
  have hd : d = Finsupp.single () (d ()) := by
    ext
    simp
  rw [hd]
  exact this

theorem FunEqHom_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} := by
  intro K _ _ _ p q σ hS f g hf0 hf1 hfE hg0 hgE
  obtain ⟨h, hh0, hh⟩ := h1 K Unit f (g : MvPowerSeries Unit K) hf0 hf1 hg0
  have hI : IntegralMv h := funEqInv h2 h3 hk hS hf0 hf1 hfE h hh0 (by
    rw [hh]
    exact funEqType_unit (q_ne_zero hS) hgE)
  exact ⟨h, hh0, fun n => hI _, hh⟩

section FG

open Formalism.G.LogP

theorem log_subst2 {R : Type*} [CommRing R] {τ : Type*} (f : PowerSeries R)
    (F : MvPowerSeries (Fin 2) R) (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF : f.subst F = atX f + atY f) {u v : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    f.subst (F.subst ![u, v]) = f.subst u + f.subst v := by
  have hb := hs2 hu hv
  rw [← psubst_subst f hF0 hb, hF, MvPowerSeries.subst_add hb, atX, atY,
    psubst_subst f (by simp) hb, psubst_subst f (by simp) hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]
  rfl

theorem psubst_zero {R : Type*} [CommRing R] {τ : Type*} (f : PowerSeries R)
    (hf0 : constantCoeff f = 0) : f.subst (0 : MvPowerSeries τ R) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf0
  have ha : PowerSeries.HasSubst (0 : MvPowerSeries τ R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.subst_mul ha, PowerSeries.subst_X ha, zero_mul]

theorem subst_zero_eq_rescale {R : Type*} [CommRing R] (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)] =
      MvPowerSeries.rescale ![0, 1] Φ := by
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  fin_cases s <;> simp

theorem cc_subst2 {R : Type*} [CommRing R] {τ : Type*} [Finite τ] (F : MvPowerSeries (Fin 2) R)
    (hF0 : MvPowerSeries.constantCoeff F = 0) {u v : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.constantCoeff (F.subst ![u, v]) = 0 := by
  have hc : ∀ s, MvPowerSeries.constantCoeff (![u, v] s) = 0 := by
    intro s
    fin_cases s <;> simp [hu, hv]
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hc) hc hF0

theorem map_subst2 {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {τ : Type*}
    (Φ : MvPowerSeries (Fin 2) A) {u v : MvPowerSeries τ A}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.map φ (Φ.subst ![u, v]) =
      (MvPowerSeries.map φ Φ).subst ![MvPowerSeries.map φ u, MvPowerSeries.map φ v] := by
  have hc : ∀ s, MvPowerSeries.constantCoeff (![u, v] s) = 0 := by
    intro s
    fin_cases s <;> simp [hu, hv]
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hc)]
  congr 1
  funext s
  fin_cases s <;> rfl

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) :
    MvPowerSeries τ (unitBall K) :=
  fun d => ⟨MvPowerSeries.coeff d F, hF d⟩

theorem coeff_lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) (d : τ →₀ ℕ) :
    ((MvPowerSeries.coeff d (lift F hF) : unitBall K) : K) = MvPowerSeries.coeff d F := rfl

theorem map_lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) :
    MvPowerSeries.map (unitBall K).subtype (lift F hF) = F := by
  ext d
  rw [MvPowerSeries.coeff_map]
  exact coeff_lift F hF d

theorem map_subtype_injective {τ : Type*} :
    Function.Injective
      (MvPowerSeries.map (unitBall K).subtype : MvPowerSeries τ (unitBall K) → MvPowerSeries τ K) := by
  intro a b h
  ext d
  have h' := congrArg (MvPowerSeries.coeff d) h
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h'
  exact h'

end FG

theorem FunEqFormalGroup_of' (hg : Formalism.G.FunEqGroup.{u}) : Formalism.G.FunEqFormalGroup.{u} := by
  intro K _ _ _ p q σ hS f hf0 hf1 hfE
  obtain ⟨F, hF0, hFI, hF⟩ := hg K p q σ hS f hf0 hf1 hfE
  have hX : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1 := by
    have e : F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = MvPowerSeries.X 0 := by
      refine substInjective K (Fin 2) f _ _ hf0 hf1 (cc_subst2 F hF0 (by simp) (by simp))
        (by simp) ?_
      rw [log_subst2 f F hF0 hF (by simp) (by simp), psubst_zero f hf0, add_zero]
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) e
    rw [Formalism.G.LogP.subst_X0_zero_eq_rescale, MvPowerSeries.coeff_rescale] at this
    simpa [Finsupp.prod_single_index, MvPowerSeries.coeff_X] using this
  have hY : MvPowerSeries.coeff (Finsupp.single 1 1) F = 1 := by
    have e : F.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] = MvPowerSeries.X 1 := by
      refine substInjective K (Fin 2) f _ _ hf0 hf1 (cc_subst2 F hF0 (by simp) (by simp))
        (by simp) ?_
      rw [log_subst2 f F hF0 hF (by simp) (by simp), psubst_zero f hf0, zero_add]
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 1 1)) e
    rw [subst_zero_eq_rescale, MvPowerSeries.coeff_rescale] at this
    simpa [Finsupp.prod_single_index, MvPowerSeries.coeff_X] using this
  set F₀ := lift F hFI with hF₀
  have hF₀0 : MvPowerSeries.constantCoeff F₀ = 0 := Subtype.ext (by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lift,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF0]
    rfl)

  have hassK : F.subst ![F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K),
      MvPowerSeries.X 1], MvPowerSeries.X 2] =
      F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K),
      F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]] := by
    have c01 := cc_subst2 F hF0 (MvPowerSeries.constantCoeff_X (R := K) (0 : Fin 3))
      (MvPowerSeries.constantCoeff_X (R := K) (1 : Fin 3))
    have c12 := cc_subst2 F hF0 (MvPowerSeries.constantCoeff_X (R := K) (1 : Fin 3))
      (MvPowerSeries.constantCoeff_X (R := K) (2 : Fin 3))
    refine substInjective K (Fin 3) f _ _ hf0 hf1
      (cc_subst2 F hF0 c01 (by simp)) (cc_subst2 F hF0 (by simp) c12) ?_
    rw [log_subst2 f F hF0 hF c01 (by simp), log_subst2 f F hF0 hF (by simp) c12,
      log_subst2 f F hF0 hF (by simp) (by simp), log_subst2 f F hF0 hF (by simp) (by simp)]
    ring
  let G : FormalGroup (unitBall K) :=
    { toPowerSeries := F₀
      zero_constantCoeff := hF₀0
      lin_coeff_X := Subtype.ext (by rw [coeff_lift, hX]; rfl)
      lin_coeff_Y := Subtype.ext (by rw [coeff_lift, hY]; rfl)
      assoc := by
        have c01 := cc_subst2 F₀ hF₀0
          (MvPowerSeries.constantCoeff_X (R := unitBall K) (0 : Fin 3))
          (MvPowerSeries.constantCoeff_X (R := unitBall K) (1 : Fin 3))
        have c12 := cc_subst2 F₀ hF₀0
          (MvPowerSeries.constantCoeff_X (R := unitBall K) (1 : Fin 3))
          (MvPowerSeries.constantCoeff_X (R := unitBall K) (2 : Fin 3))
        apply map_subtype_injective
        rw [map_subst2 _ _ c01 (by simp), map_subst2 _ _ (by simp) c12,
          map_subst2 _ _ (by simp) (by simp), map_subst2 _ _ (by simp) (by simp)]
        simp only [MvPowerSeries.map_X, hF₀, map_lift]
        exact hassK }
  refine ⟨G, hf0, hf1, ?_⟩
  show f.subst (MvPowerSeries.map (unitBall K).subtype F₀) = atX f + atY f
  rw [hF₀, map_lift]
  exact hF

end Formalism.LT.Asm

namespace Formalism.LT

theorem FunEqGroup_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqGroup.{u} :=
  Formalism.LT.Asm.FunEqGroup_of' h1 h2 h3 hk

theorem FunEqFormalGroup_of (hg : Formalism.G.FunEqGroup.{u}) : Formalism.G.FunEqFormalGroup.{u} :=
  Formalism.LT.Asm.FunEqFormalGroup_of' hg

theorem FunEqHom_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} :=
  Formalism.LT.Asm.FunEqHom_of' h1 h2 h3 hk

end Formalism.LT
