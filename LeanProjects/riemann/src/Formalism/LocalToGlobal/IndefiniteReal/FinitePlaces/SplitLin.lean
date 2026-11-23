import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem facts_at_e₁ (hPD : PlaceLatDual D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e e₁ : AE D}
    (he : IsIdemSum e P) (he₁ : IsSplitIdem D e₁) (h1 : e₁ * e = e₁) :
    (∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => e₁ * a) ∈ latAll S T ΛS ΛT) ∧
    (∀ x ∈ latAll S T ΛS ΛT, IsHalf e₁ x → ∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1) ∧
    (∀ y, IsHalf (cA D e₁) y → (∀ x ∈ latAll S T ΛS ΛT, IsHalf e₁ x → ψ (symplO S T x y) = 1) →
      y ∈ latAll S T ΛS ΛT) ∧
    (∀ x, IsHalf e₁ x → (∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1) →
      x ∈ latAll S T ΛS ΛT) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf (cA D e₁) v ∧ u = r + k • v) ∧
    (∀ x, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT) ∧
    (∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ latAll S T ΛS ΛT) := by
  classical
  obtain ⟨hi, -, hP⟩ := hPD ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hd2, hd3, hfin, hop⟩ := hP P e he
  have hc₁ := isSplitIdem_cA he₁
  have hmapH : ∀ (f : AE D), f * f = f → ∀ u : WO S T, IsHalf f (u.map (fun a => f * a)) := fun f hf u i j => by
    simp only [Matrix.map_apply]; rw [← mul_assoc, hf]
  have hmapId : ∀ (f : AE D) (u : WO S T), IsHalf f u → u.map (fun a => f * a) = u := fun f u hu => by
    ext i j; exact hu i j
  have hfinE : ∀ (f f' : AE D), f' * f' = f' → (∀ u : WO S T, IsHalf f' u → IsHalf f u) →
      (∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => f' * a) ∈ latAll S T ΛS ΛT) →
      (∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf f u →
        ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf f v ∧ u = r + k • v) →
      ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf f' u →
        ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf f' v ∧ u = r + k • v := by
    intro f f' hf' hsub hmul hF k hk
    obtain ⟨R, hR⟩ := hF k hk
    refine ⟨R.image (fun r => r.map (fun a => f' * a)), fun u hu hue => ?_⟩
    obtain ⟨r, hr, v, hv, -, huv⟩ := hR u hu (hsub u hue)
    refine ⟨r.map (fun a => f' * a), Finset.mem_image_of_mem _ hr, v.map (fun a => f' * a), hmul v hv,
      hmapH f' hf' v, ?_⟩
    rw [← hmapId f' u hue, huv]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    ring
  refine ⟨fun u hu => hi e₁ he₁ u hu, fun x hx hxe y hy hye => (hd2 y (chalf_sub_of S T h1 hye)).2 hy x hx
    (half_sub_of S T h1 hxe), fun y hye H => (hd2 y (chalf_sub_of S T h1 hye)).1 fun x hx _ => ?_,
    fun x hxe H => (hd3 x (half_sub_of S T h1 hxe)).1 fun y hy _ => ?_,
    hfinE e e₁ he₁.1 (fun u hu => half_sub_of S T h1 hu) (hi e₁ he₁) (fun k hk => hfin k hk e (Or.inl rfl)),
    hfinE (cA D e) (cA D e₁) hc₁.1 (fun u hu => chalf_sub_of S T h1 hu) (hi (cA D e₁) hc₁)
      (fun k hk => hfin k hk (cA D e) (Or.inr rfl)),
    fun x hx => hop e (Or.inl rfl) x (half_sub_of S T h1 hx),
    fun y hy => hop (cA D e) (Or.inr rfl) y (chalf_sub_of S T h1 hy)⟩
  · rw [symplO_left_e₁ S T hye]
    exact H _ (hi e₁ he₁ x hx) (hmapH e₁ he₁.1 x)
  · rw [symplO_right_ce₁ S T hxe]
    exact H _ (hi (cA D e₁) hc₁ y hy) (hmapH (cA D e₁) hc₁.1 y)

open Classical in

theorem splitLin_of (hPD : PlaceLatDual D) (hlev : LatLevel D) : SplitLin D := by
  intro ψ S T χS χT om hω ΛS ΛT hS hT P e he f₀ hf₀ hvac Tm hTm e₁ he₁ h1 g h hg hh x y hx hy
  have hψ := hω.std
  obtain ⟨hΛe₁, hLL₁, hdY₁, hdX₁, hfX₁, hfY₁, -, hoY₁⟩ := facts_at_e₁ hPD hψ S T hS hT he he₁ h1
  obtain ⟨-, hvi, hP⟩ := hPD ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hd2, -, -, -⟩ := hP P e he
  obtain ⟨Tc, -, huniq, htheta, -⟩ :=
    placeModelAt_of hPD ψ hψ S T ΛS ΛT hS hT P e he f₀ hf₀ hvac e (Or.inl rfl)
  have hthm : ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsThetaFunO ψ S T (Tm Φ) := fun Φ hΦ => by
    rw [huniq Tm hTm Φ hΦ]; exact htheta Φ hΦ
  obtain ⟨r, hr, hsplit⟩ := hω.om_split e₁ he₁ g h hg hh x y hx hy
  set c : ℂ := (r : ℂ) * (splitFacO χS χT x y : ℂ) with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne') (Circle.coe_ne_zero _)
  obtain ⟨k₁, hk₁, h₁⟩ := hvi e₁ he₁ g h hg hh
  obtain ⟨k₂, hk₂, h₂⟩ := hvi e₁ he₁ g⁻¹ h⁻¹ (suppAt_inv_fp hg) (suppAt_inv_fp hh)
  have h₁' : ∀ t ∈ latAll S T ΛS ΛT, k₁ • actO S T g⁻¹⁻¹ h⁻¹⁻¹ t ∈ latAll S T ΛS ΛT := by
    simpa only [inv_inv] using h₁
  have hSBp : ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
      IsSBHalf e (latAll S T ΛS ΛT) (fun t => Φ (actO S T g h t)) :=
    fun Φ hΦ => sb_comp S T g h hk₁ h₁ hk₂ h₂ hΦ
  have hSBq : ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
      IsSBHalf e (latAll S T ΛS ΛT) (fun t => Φ (actO S T g⁻¹ h⁻¹ t)) :=
    fun Φ hΦ => sb_comp S T g⁻¹ h⁻¹ hk₂ h₂ hk₁ h₁' hΦ
  have hindSB : IsSBHalf e (latAll S T ΛS ΛT) (halfInd e (latAll S T ΛS ΛT)) :=
    (isSBHalf_iff S T).2 Four.isSB_ind
  have hf₀T : Tm (halfInd e (latAll S T ΛS ΛT)) = f₀ := by
    have := hTm.vac
    rwa [one_smul] at this

  have hG := hSBp _ hindSB
  have hG₁ := hthm _ hG
  have hw : om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) = c • f₀ := by
    by_contra hne
    have hw0 : om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) - c • f₀ ≠ 0 :=
      sub_ne_zero.2 hne
    have hwθ : IsThetaFunO ψ S T (om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) -
        c • f₀) := by
      rw [sub_eq_add_neg, ← neg_smul]
      exact Formalism.IndefR.Eqv.thetaO_add (hω.om_pres _ _ hG₁) (Formalism.IndefR.Eqv.thetaO_smul _ hf₀)

    have hfixG : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e₁ u ∨ IsHalf (cA D e₁) u) →
        heisO ψ S T (actO S T g⁻¹ h⁻¹ u) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) =
          Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t)) := by
      intro u hu hue
      rcases hue with hue | hue
      · have hqu : IsHalf e (actO S T g⁻¹ h⁻¹ u) := isHalf_actO_fp S T _ _ (half_sub_of S T h1 hue)
        rw [← hTm.trans _ hG _ hqu]
        congr 1
        funext t
        rw [Formalism.IndefR.Eqv.actO_add, Formalism.IndefR.Eqv.actO_inv_actO, halfInd_add S T hu (half_sub_of S T h1 hue)]
      · have hqu : IsHalf (cA D e) (actO S T g⁻¹ h⁻¹ u) := isHalf_actO_fp S T _ _ (chalf_sub_of S T h1 hue)
        rw [← hTm.modul _ hG _ hqu]
        congr 1
        funext t
        by_cases hc : actO S T g h t ∈ latAll S T ΛS ΛT ∧ IsHalf e (actO S T g h t)
        · have h1' : symplO S T t (actO S T g⁻¹ h⁻¹ u) = symplO S T (actO S T g h t) u := by
            rw [← Formalism.IndefR.Eqv.symplO_actO S T g h t (actO S T g⁻¹ h⁻¹ u), Formalism.IndefR.Eqv.actO_inv_actO]
          rw [h1', (hd2 u (chalf_sub_of S T h1 hue)).2 hu _ hc.1 hc.2, one_mul]
        · have : halfInd e (latAll S T ΛS ΛT) (actO S T g h t) = 0 := by unfold halfInd; rw [if_neg hc]
          rw [this, mul_zero]
    have hfix : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e₁ u ∨ IsHalf (cA D e₁) u) →
        heisO ψ S T u (om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) - c • f₀) =
          om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) - c • f₀ := by
      intro u hu hue
      have e1 := hω.om_heis g h (actO S T g⁻¹ h⁻¹ u) _ hG₁
      rw [Formalism.IndefR.Eqv.actO_inv_actO, hfixG u hu hue] at e1
      have e2 : heisO ψ S T u f₀ = f₀ := hvac u hu (hue.imp (half_sub_of S T h1) (chalf_sub_of S T h1))
      rw [← heisL_apply, map_sub, map_smul, heisL_apply, heisL_apply, ← e1, e2]
    obtain ⟨ℓ, hℓ, hℓw⟩ := exists_invForm ψ S T e₁ he₁.2.1 (latAll S T ΛS ΛT) hLL₁ hdY₁ hfX₁ hfY₁ hoY₁
      (fun f hf => by
        obtain ⟨k, hk, hk'⟩ := hlev ψ hψ S T ΛS ΛT hS hT f hf
        exact ⟨k, hk, fun u hu _ => hk' u hu⟩)
      hwθ (fun u hu hue => hfix u hu (Or.inl hue)) (fun u hu hue => hfix u hu (Or.inr hue)) hw0
    apply hℓw
    have hΨSB : IsSBHalf e (latAll S T ΛS ΛT)
        ((fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t)) - halfInd e (latAll S T ΛS ΛT)) := by
      rw [sub_eq_add_neg, ← neg_one_smul ℂ (halfInd e (latAll S T ΛS ΛT))]
      exact (isSBHalf_iff S T).2 (((isSBHalf_iff S T).1 hG).add (((isSBHalf_iff S T).1 hindSB).smul (-1)))
    have hev := evalYZero_zero S T ψ he₁ h1 (latAll S T ΛS ΛT) hΛe₁ hLL₁ hdX₁ hfY₁ Tm hTm.modul hthm ℓ hℓ hΨSB
      (fun t ht h0 => by
        show halfInd e (latAll S T ΛS ΛT) (actO S T g h t) - halfInd e (latAll S T ΛS ΛT) t = 0
        rw [actO_fix S T he.2 h1 hg hh ht h0, sub_self])
    rw [map_sub, map_sub, hf₀T] at hev
    rw [map_sub, map_smul, hsplit ℓ hℓ _ hG₁, smul_eq_mul, ← mul_sub, hev, mul_zero]

  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    c⁻¹ • ((om (g, h)).comp (Tm.comp (Formalism.IndefR.Eqv.pull S T g h)))
  have hTm'ap : ∀ Φ, Tm' Φ = c⁻¹ • om (g, h) (Tm (fun t => Φ (actO S T g h t))) := fun Φ => rfl
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm' := by
    refine ⟨fun Φ hΦ x₀ hx₀ => ?_, fun Φ hΦ y₀ hy₀ => ?_, ?_⟩
    · rw [hTm'ap, hTm'ap]
      have hq : IsHalf e (actO S T g⁻¹ h⁻¹ x₀) := isHalf_actO_fp S T _ _ hx₀
      have e1 : (fun t => Φ (actO S T g h t + x₀)) =
          fun t => Φ (actO S T g h (t + actO S T g⁻¹ h⁻¹ x₀)) := by
        funext t; rw [Formalism.IndefR.Eqv.actO_add, Formalism.IndefR.Eqv.actO_inv_actO]
      show c⁻¹ • om (g, h) (Tm (fun t => Φ (actO S T g h t + x₀))) = _
      rw [e1, hTm.trans _ (hSBp Φ hΦ) _ hq, hω.om_heis g h _ _ (hthm _ (hSBp Φ hΦ)),
        Formalism.IndefR.Eqv.actO_inv_actO, ← heisL_apply, ← heisL_apply, map_smul]
    · rw [hTm'ap, hTm'ap]
      have hq : IsHalf (cA D e) (actO S T g⁻¹ h⁻¹ y₀) := isHalf_actO_fp S T _ _ hy₀
      have e1 : (fun t => ψ (symplO S T (actO S T g h t) y₀) * Φ (actO S T g h t)) =
          fun t => ψ (symplO S T t (actO S T g⁻¹ h⁻¹ y₀)) * Φ (actO S T g h t) := by
        funext t
        rw [← Formalism.IndefR.Eqv.symplO_actO S T g h t (actO S T g⁻¹ h⁻¹ y₀), Formalism.IndefR.Eqv.actO_inv_actO]
      show c⁻¹ • om (g, h) (Tm (fun t => ψ (symplO S T (actO S T g h t) y₀) * Φ (actO S T g h t))) = _
      rw [e1, hTm.modul _ (hSBp Φ hΦ) _ hq, hω.om_heis g h _ _ (hthm _ (hSBp Φ hΦ)),
        Formalism.IndefR.Eqv.actO_inv_actO, ← heisL_apply, ← heisL_apply, map_smul]
    · rw [one_smul, hTm'ap]
      show c⁻¹ • om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) = f₀
      rw [hw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨r, hr, fun Φ hΦ => ?_, fun hstab hnorm => ?_⟩
  · have e1 := huniq Tm' hTm' _ (hSBq Φ hΦ)
    have e2 := huniq Tm hTm _ (hSBq Φ hΦ)
    rw [← e2, hTm'ap] at e1
    have e3 : (fun t => (fun t => Φ (actO S T g⁻¹ h⁻¹ t)) (actO S T g h t)) = Φ := by
      funext t; exact congrArg Φ (Formalism.IndefR.Eqv.actO_actO_inv S T g h t)
    rw [e3] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  · obtain ⟨μ, 𝓕, ⟨hHaar, hFD, -⟩, hn⟩ := hnorm
    have hindeq : (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t)) = halfInd e (latAll S T ΛS ΛT) := by
      funext t
      unfold halfInd
      by_cases ht : IsHalf e t
      · have h2 := (isHalf_actO_iff S T g h t).2 ht
        simp only [hstab t ht, ht, h2, and_true]
      · have h2 : ¬ IsHalf e (actO S T g h t) := fun h' => ht ((isHalf_actO_iff S T g h t).1 h')
        simp only [ht, h2, and_false, if_false]
    rw [hindeq, hf₀T] at hw
    have hU := hω.om_unit μ 𝓕 hHaar hFD (g, h) f₀ hf₀
    rw [hw] at hU
    have hn' : ∫ w in 𝓕, ‖f₀ w‖ ^ 2 ∂μ = 1 := hn
    have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (μ.restrict 𝓕) := by
      by_contra hni
      rw [integral_undef hni] at hn'
      exact zero_ne_one hn'
    have hI : ∫⁻ w in 𝓕, ‖f₀ w‖ₑ ^ 2 ∂μ = 1 := by
      have h3 := ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun w => by simp only [Pi.zero_apply]; positivity)
      rw [hn', ENNReal.ofReal_one] at h3
      rw [h3]
      congr 1
      funext w
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    have hsm : (fun w => ‖(c • f₀) w‖ₑ ^ 2) = fun w => ‖c‖ₑ ^ 2 * ‖f₀ w‖ₑ ^ 2 := by
      funext w
      rw [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    rw [hsm, lintegral_const_mul' _ _ (by simp), hI, mul_one] at hU
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_eq_one] at hU
    have hcn : ‖c‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 hU
    have hsf : ‖(splitFacO χS χT x y : ℂ)‖ = 1 := Circle.norm_coe _
    rw [hcdef, norm_mul, hsf, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hcn
    exact hcn

end Formalism.IndefR.Fin

end
