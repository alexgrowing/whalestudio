import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
import Formalism.RankGapBounds.RankGapProofs.WeightedMeanData
import Formalism.RankGapBounds.RankGapProofs.UniformMeanTopLine

open Real

namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds

open Formalism.RankGapBounds.WeightedMeanData

noncomputable section

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)

def Lam5 (u0 : U0) : ℝ :=
  (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
    - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)

def K5v5 (u0 : U0) : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k) + (m : ℝ) * (D.sumA * D.lg + C.cE * D.B0)
    + D.SDiv - D.sumA * Lam5 D C u0 + D.EDiv C

def K0v5 : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + D.EDiv C + (m : ℝ) * C.cE * D.B0 + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)

def K7v5 : ℝ :=
  C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L) + C.cSl1 * Xpp + 1

lemma exponent_le_upper (hE : EComp5 D C) (u0 : U0) (u : W u0) :
    D.Ee u0 u ≤ (m : ℝ) * (D.sumA * D.lg + C.cE * D.B0) := by
  have := (abs_le.mp (hE u0 u)).2
  linarith

lemma exponent_ge_lower (hE : EComp5 D C) (u0 : U0) (u : W u0) :
    (m : ℝ) * (D.sumA * D.lg - C.cE * D.B0) ≤ D.Ee u0 u := by
  have := (abs_le.mp (hE u0 u)).1
  linarith

lemma losses_of_losses5 [Nonempty U0] (h : LossBounds D C) : D.Losses C := by
  refine ⟨?_, ?_⟩
  · have := umean_mono (X := fun u0 => D.ASK u0 - D.Ga u0) (Y := fun _ : U0 => D.LoP C)
      (fun u0 => (h u0).1)
    rwa [umean_const] at this
  · have := umean_mono (X := D.IO) (Y := fun _ : U0 => D.LoP C) (fun u0 => (h u0).2)
    rwa [umean_const] at this

lemma s_lower5 (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.Ga u0 + D.muCC u0 - K5v5 D C u0 - wmean (D.d u0) (Lo5 D C Xpp u0) ≤ D.s u0 := by
  have hA := D.sumA_nonneg C hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, -⟩ := hS
  unfold Data.s
  refine sub_wmean_le (hd u0) _ (fun u => ?_)
  have h1 := (hSN u0 u).2
  have h2 := hDIV u0 u
  rw [Finset.sum_sub_distrib, Data.sum_aT_mul] at h2
  have h3 : Lam5 D C u0 ≤ Real.log (D.T u0 u) := (hCount u0 u).1
  have h4 := mul_le_mul_of_nonneg_left h3 hA
  have h5 := exponent_le_upper D C hE u0 u
  have h6 := (hSl u0 u).1
  unfold K5v5 Data.SDiv Data.EDiv
  try dsimp only
  linarith

lemma Vvar_bound5 (hS : D.HidaSetting C) (hE : EComp5 D C) (hH : D.HComp C) (hCount : Count5 D C)
    (u0 : U0) (u u' : W u0) :
    (-D.Ee u0 u - D.h u0 u) - (-D.Ee u0 u' - D.h u0 u') ≤ D.Vvar C := by
  have hA := D.sumA_nonneg C hS
  have h1 := exponent_le_upper D C hE u0 u'
  have h2 := exponent_ge_lower D C hE u0 u
  have h3 := (abs_le.mp (hH u0 u' u)).2
  rw [Data.sum_aT_mul, Data.sum_aT_mul] at h3
  have h4 := (abs_le.mp ((hCount u0 u).2.2 u')).2
  have h5 := mul_le_mul_of_nonneg_left h4 hA
  unfold Data.Vvar
  linarith

lemma u_function_le_mean (hS : D.HidaSetting C) (hE : EComp5 D C) (hH : D.HComp C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.uF u0 ≤ D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) := by
  have hd := hS.2.2.2.2.2.2.2.2.2.1
  have hs : ∀ u, (D.muMaxN u0 u - D.h u0 u - D.K3 C) - wmean (D.d u0) (Lo5 D C Xpp u0)
      ≤ D.s u0 := by
    intro u
    unfold Data.s
    refine sub_wmean_le (hd u0) _ (fun u' => ?_)
    have h1 := (hSN u0 u).1
    have h2 := (hSN u0 u').2
    have h3 := (hSl u0 u).2
    have h4 := (hSl u0 u').1
    have h5 := Vvar_bound5 D C hS hE hH hCount u0 u u'
    unfold Data.K3
    try dsimp only
    linarith
  unfold Data.uF
  have hsup := Finset.sup'_le (Finset.univ_nonempty (α := W u0))
    (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)
    (a := D.s u0 + (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0)))
    (fun u _ => by have := hs u; linarith)
  linarith

lemma key_identity5 (hv : 0 < D.v) (hf : 0 < f) (u0 : U0) (hw : ∀ j ρ, 0 < D.w u0 j ρ) :
    D.SDiv - D.sumA * Lam5 D C u0 + (m : ℝ) * D.sumA * D.lg =
      D.Main u0 + D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) := by
  have h := D.key_identity C hv hf u0 hw
  unfold Data.abelian₂ at h
  unfold Lam5
  linear_combination h

lemma Ga_bound5 (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C)
    (hH : D.HComp C) (hCount : Count5 D C) (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hSI : D.SlopeIneq) (hHH : D.HHBound C) (hFP : D.FParams) (u0 : U0) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + K0v5 D C
      + wmean (D.d u0) (Lo5 D C Xpp u0)
      + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) := by
  have hsl := s_lower5 D C Xpp hS hDIV hE hCount hSl hSN u0
  have huF0 := D.uF_nonneg C hS u0
  have huF := u_function_le_mean D C Xpp hS hE hH hCount hSl hSN u0
  obtain ⟨hx, hb, -, -, -, hv, hf, -, hw, -, -, -, -, hdelBar, hetaBar, heBar0, heBar⟩ := hS
  have hid := key_identity5 D C hv hf u0 (hw u0)
  obtain ⟨hdel0, hdelle, heta0, hetale, he0, hele⟩ := hFP u0
  obtain ⟨hHH1, hHH2, hHH3⟩ := hHH u0
  have hSI' := hSI u0 hdel0 (by linarith) heta0 he0 (by linarith) hHH1 hHH2
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hphi := phi_bound huF0 hHH2 hHH3 hb hX huF
  have hA0 : 0 ≤ 4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) :=
    mul_nonneg (by linarith)
      (Real.log_nonneg (by have := div_nonneg hHH2.le huF0; linarith))
  have hsq : Real.sqrt (D.e u0) ≤ Real.sqrt D.eBar := Real.sqrt_le_sqrt hele
  have hc0 : 0 ≤ D.η u0 + 4 * Real.sqrt (D.e u0) :=
    add_nonneg heta0 (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hc1 : 0 ≤ D.etaBar + 4 * Real.sqrt D.eBar :=
    add_nonneg hetaBar (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hB : (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
      ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
    calc (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
        ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * D.HH u0 :=
          mul_le_mul_of_nonneg_right (by linarith) hHH2.le
      _ ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
          mul_le_mul_of_nonneg_left hHH3 hc1
  have hB0 : 0 ≤ (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 := mul_nonneg hc0 hHH2.le
  have hinv : (1 - D.del u0)⁻¹ ≤ (1 - D.delBar)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hPhi : (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
        + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0)
      ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) :=
    calc _ ≤ (1 - D.delBar)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) :=
          mul_le_mul_of_nonneg_right hinv (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hinv0
  unfold K0v5
  unfold K5v5 at hsl
  linarith

lemma weighted_mean_lower_bound_le (hS : D.HidaSetting C) (hCount : Count5 D C) (u0 : U0) :
    wmean (D.d u0) (Lo5 D C Xpp u0) ≤ C.cSl1 * D.IO u0 + K7v5 D C Xpp := by
  obtain ⟨-, -, ha, hb', hk, -, -, -, -, hd, -, -, hcSl1, -⟩ := hS
  refine wmean_le_const (hd u0) _ (fun u => ?_)
  have hc : 0 ≤ C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') :=
    mul_nonneg (mul_nonneg (mul_nonneg hcSl1 D.nT_nonneg) (Nat.cast_nonneg _))
      (add_nonneg (div_nonneg ha hk.le) hb')
  have h1 := mul_le_mul_of_nonneg_left (hCount u0 u).2.1 hc
  unfold Lo5 K7v5
  linarith

end

theorem each_unit_bound_statement {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : PointwiseBoundVariant D C Xpp := by
  intro hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP u0
  have hx : 0 < D.x := hS.1
  have hdelBar : D.delBar < 1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcSl1 : 0 ≤ C.cSl1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hLX : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) :=
    mul_nonneg hinv0 (mul_nonneg (by norm_num) hLX)
  have h1 := Ga_bound5 D C Xpp hS hDIV hE hH hCount hSl hSN hSI hHH hFP u0
  have h2 := weighted_mean_lower_bound_le D C Xpp hS hCount u0
  have hIO := mul_le_mul_of_nonneg_left (hLoss u0).2 hcSl1
  have hML : wmean (D.d u0) (Lo5 D C Xpp u0) ≤ MLo5 D C Xpp := by
    unfold MLo5; unfold K7v5 at h2; linarith
  have h3 := mul_le_mul_of_nonneg_left hML hc4
  have h4 := (hLoss u0).1
  unfold Data.K3 at h1
  unfold K0v5 Data.EDiv at h1
  unfold ErrX5at UBar5
  linarith

theorem weighted_mean_bound_statement {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : MeanBoundOfLossBounds D C Xpp := by
  intro hne hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
  have := hne
  have hx : 0 < D.x := hS.1
  have hdelBar : D.delBar < 1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcSl1 : 0 ≤ C.cSl1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hLX : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) :=
    mul_nonneg hinv0 (mul_nonneg (by norm_num) hLX)
  have hp : 0 ≤ (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1 :=
    mul_nonneg (by linarith) hcSl1
  have hGa : ∀ u0, D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ)
      + ((1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1) * D.IO u0
      + 0 * D.IO u0
      + (K0v5 D C + (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * K7v5 D C Xpp
        + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) * (D.K3 C + D.b)
        + (1 - D.delBar)⁻¹ * ((D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))) := by
    intro u0
    have h1 := Ga_bound5 D C Xpp hS hDIV hE hH hCount hSl hSN hSI hHH hFP u0
    have h2 := weighted_mean_lower_bound_le D C Xpp hS hCount u0
    have h3 := mul_le_mul_of_nonneg_left h2 hc4
    linarith
  have h1 := umean_le_comb (X := D.Ga) (A := D.Main)
    (B := fun u0 => Real.log (Fintype.card (W u0) : ℝ)) (P := D.IO) (E := D.IO) _ _ _ hGa
  have h2 := umean_le_comb (X := D.ASK) (A := fun u0 => D.ASK u0 - D.Ga u0) (B := D.Ga)
    (P := D.Ga) (E := D.Ga) 0 0 0 (fun i => by
      show D.ASK i ≤ (D.ASK i - D.Ga i) + D.Ga i + 0 * D.Ga i + 0 * D.Ga i + 0
      linarith)
  have h3 := mul_le_mul_of_nonneg_left hLoss.2 hp
  have h4 := hLoss.1
  unfold K0v5 Data.K3 K7v5 Data.EDiv at h1
  unfold errorTermWith UBar5 MLo5
  linarith

theorem uniform_bound_statement {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : MeanBoundWith D C Xpp := by
  intro hne hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
  exact weighted_mean_bound_statement D C Xpp hne hS hDIV hE hH hCount hSl hSN
    (losses_of_losses5 D C hLoss) hSI hHH hFP

def C1 : Consts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

end Formalism.LFunctionChainParameters.WeightedSlopeBounds
