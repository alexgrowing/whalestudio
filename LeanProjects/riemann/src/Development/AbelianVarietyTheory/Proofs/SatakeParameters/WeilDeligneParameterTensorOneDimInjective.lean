import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne TensorProduct

namespace GlobalTheory.WeilDeligne.TwistInj

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem apply_eq_det_smul (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ) :
    f v = LinearMap.det f • v := by
  have hd : LinearMap.det f = f (Pi.single 0 1) 0 := by
    conv_lhs => rw [← Matrix.toLin'_toMatrix' f]
    rw [LinearMap.det_toLin', Matrix.det_fin_one, LinearMap.toMatrix'_apply]
  have hv : v = v 0 • (Pi.single 0 1 : Fin 1 → ℂ) := by
    funext i; fin_cases i; simp
  funext i; fin_cases i
  rw [hv, map_smul, hd]
  simp [mul_comm]

def chr (c : WDRep h (Fin 1 → ℂ)) : Weil h →* ℂˣ :=
  (Units.map (LinearMap.det : Module.End ℂ (Fin 1 → ℂ) →* ℂ)).comp c.ρ.asGroupHom

theorem coe_chr (c : WDRep h (Fin 1 → ℂ)) (σ : Weil h) :
    (chr c σ : ℂ) = LinearMap.det (c.ρ σ) := by
  simp [chr, Representation.asGroupHom_apply]

theorem isSmooth_chr (c : WDRep h (Fin 1 → ℂ)) : IsSmooth (chr c) :=
  c.smooth.of_le fun σ hσ => Units.ext (by rw [coe_chr, hσ, map_one]; rfl)

theorem N_eq_zero (c : WDRep h (Fin 1 → ℂ)) : c.N = 0 := by
  have hz : LinearMap.det (0 : Module.End ℂ (Fin 1 → ℂ)) = 0 := by
    have := congrFun (apply_eq_det_smul 0 (fun _ => 1)) 0
    simpa using this.symm
  obtain ⟨k, hk⟩ := c.nilpotent
  have h0 : LinearMap.det c.N = 0 := by
    have : LinearMap.det c.N ^ k = 0 := by rw [← map_pow, hk, hz]
    exact pow_eq_zero_iff'.mp this |>.1
  refine LinearMap.ext fun v => ?_
  rw [apply_eq_det_smul, h0, zero_smul]
  rfl

theorem tensor_iso_twist {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (c : WDRep h (Fin 1 → ℂ)) :
    (a.tensor c).Iso (a.twist (chr c) (isSmooth_chr c)) := by
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ V) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [WDRep.tensor_ρ, TensorProduct.map_tmul, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.funUnique_apply,
        TensorProduct.rid_tmul, WDRep.twist_ρ, LinearMap.smul_apply, map_smul, coe_chr]
      rw [apply_eq_det_smul (c.ρ σ) y, smul_smul]
      simp [Function.eval, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [N_eq_zero c, Function.eval]
    | add x y hx hy => simp only [map_add, hx, hy]

theorem iso_of_twist {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {a : WDRep h V} {b : WDRep h V'} (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ)
    (hab : (a.twist χ hχ).Iso (b.twist χ hχ)) : a.Iso b := by
  obtain ⟨e, h1, h2⟩ := hab
  refine ⟨e, fun σ v => ?_, h2⟩
  have := h1 σ v
  simp only [WDRep.twist_ρ, LinearMap.smul_apply, map_smul] at this
  exact smul_right_injective V' (Units.ne_zero (χ σ)) this

end GlobalTheory.WeilDeligne.TwistInj

open GlobalTheory.WeilDeligne.TwistInj in

theorem GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), c.lpDim = 1 → a.lpChar c = b.lpChar c → a = b := by
  intro E Ω _ _ _ _ _ A w h a b c hc hab
  induction a using WD.ind with
  | hP n a =>
  induction b using WD.ind with
  | hP m b =>
  induction c using WD.ind with
  | hP k c =>
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hc
  subst hc
  rw [WD.lpChar_mk, WD.lpChar_mk, WD.mk_eq_mk] at hab
  exact WD.sound (iso_of_twist (chr c) (isSmooth_chr c)
    (((tensor_iso_twist a c).symm.trans hab).trans (tensor_iso_twist b c)))
