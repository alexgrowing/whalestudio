import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CriticalThresholdLowerBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaFactorisation

namespace Formalism.FourierDecayAlt.P.Sz7

open Finset Formalism.FourierDecayAlt.Sz

private lemma vthp_nonneg_of_ok (c : Cfg) (h : c.Ok) : 0 ≤ c.vthp := by
  unfold Cfg.vthp
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith)) hbp.le
  · exact le_refl _

private lemma vthp_le_one_tenth_of_small (c : Cfg) (h : c.Ok) (bb : ℝ) (hs : c.Small bb) : c.vthp ≤ 1 / 10 := by
  unfold Cfg.vthp
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hm : (2:ℝ) ≤ c.m := by exact_mod_cast h.hm
    have hk : (0:ℝ) ≤ c.k := Nat.cast_nonneg _
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    have hv := hs.hvth
    unfold Cfg.vth at hv
    rw [div_le_iff₀ (by linarith)] at hv
    rw [div_le_iff₀ hbp]
    have hkD : 0 ≤ (c.k:ℝ) * c.Del := mul_nonneg hk (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hm hkD]
  · norm_num

theorem aZeroBound : AZeroBound := by
  intro c bb h hs
  have hv0 := vthp_nonneg_of_ok c h
  have hv1 := vthp_le_one_tenth_of_small c h bb hs
  have hW : 0 < 1 + c.vthp := by linarith
  have hE2 : (9:ℝ) / 10 ≤ Real.exp (-(2 * c.m * Real.log bb / c.k)) := by
    have := Real.add_one_le_exp (-(2 * c.m * Real.log bb / c.k))
    linarith [hs.hmu]
  have hE1 : Real.exp c.vth ≤ 10 / 9 := by
    have h1 := Real.add_one_le_exp (-c.vth)
    have h2 : Real.exp c.vth * Real.exp (-c.vth) = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos c.vth
    have h4 := hs.hvth
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le, mul_nonneg h3.le (by linarith : (0:ℝ) ≤ 1 / 10 - c.vth)]
  have hS : Real.sqrt (14 / 5) ≤ 1.6734 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 14 / 5 by norm_num), Real.sqrt_nonneg (14 / 5)]
  have hSE : Real.sqrt (14 / 5) * Real.exp c.vth ≤ 1.6734 * (10 / 9) :=
    mul_le_mul hS hE1 (Real.exp_pos _).le (by norm_num)
  have hcOne : 0 < cOne c bb := by
    unfold cOne
    exact div_pos (by positivity) hW
  have hcLow : 0.38 * (9 / 10) / (11 / 10) ≤ cOne c bb := by
    unfold cOne
    rw [le_div_iff₀ hW]
    have : 0.38 * (9 / 10) / (11 / 10) * (1 + c.vthp) ≤ 0.38 * (9 / 10) := by
      have : (1 + c.vthp) ≤ 11 / 10 := by linarith
      nlinarith
    linarith
  refine ⟨?_, ?_⟩
  · unfold AZero
    exact div_pos (by positivity) hcOne
  · unfold AZero
    rw [div_le_iff₀ hcOne]
    nlinarith [hSE, hcLow]

lemma rho_nonneg (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l i : ℕ) (h : c.Ok)
    (hlk : l + 2 ≤ c.k) (hY : Y ∈ c.cutI l) : 0 ≤ c.rho de de' (-Y) i := by
  unfold Cfg.rho
  split_ifs with ht
  · obtain ⟨h1, _⟩ := h.htop ht.1
    have hY' : 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ c.Del / 2 := hY
    have hD : (1:ℝ) ≤ c.Del := h.hDel
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hv : 4 * c.Del ≤ c.v l := by
      unfold Cfg.v
      have hkl : (l:ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
      nlinarith [h.hv0, mul_nonneg (by linarith : (0:ℝ) ≤ c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 2 - l)]
    exact div_nonneg (Real.sqrt_nonneg _) (by linarith [hY'.2])
  · exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private lemma one_le_b_of_ok (c : Cfg) (h : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
  intro j
  induction j with
  | zero => intro h1; omega
  | succ n ih =>
    intro h1 h2
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using h.hb1
    · have e1 := ih hn (by omega)
      have e2 := h.hgap n hn (by omega)
      linarith

lemma prodb_pos (c : Cfg) (h : c.Ok) : 0 < c.prodb := by
  unfold Cfg.prodb
  exact Finset.prod_pos (fun j hj => by
    rw [Finset.mem_Icc] at hj
    linarith [one_le_b_of_ok c h j hj.1 hj.2])

lemma edge_bound (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l : ℕ) (h : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') (hl : 1 ≤ l) (hlk : l + 2 ≤ c.k) (hY : Y ∈ c.cutI l) :
    0 < c.aeff ∧ c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ 8 / c.aeff := by
  obtain ⟨hU0, hU1, hU2⟩ := edgeFactorBound c Y l h hl hlk hY
  have hr0 := rho_nonneg c de de' Y l (c.k - 1) h hlk hY
  have hD : (1:ℝ) ≤ c.Del := h.hDel
  have hkR : (4:ℝ) ≤ c.k := by exact_mod_cast h.hk
  have hv1 : 0 ≤ c.v 1 := by
    unfold Cfg.v
    push_cast
    nlinarith [h.hv0, mul_nonneg (by linarith : (0:ℝ) ≤ c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 2)]
  have ha : 4 * c.k * c.Del ≤ c.a - c.v 1 := h.ha
  have h4 : 0 < 4 * (c.k:ℝ) * c.Del := mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hapos : 0 < c.a - c.v 1 := by linarith
  have hapos' : 0 < c.a := by linarith
  cases htop : c.top
  · have haeff : c.aeff = c.a - c.v 1 := by simp [Cfg.aeff, htop]
    rw [haeff]
    refine ⟨hapos, ?_⟩
    have hr1 := positionAfter c de de' Y l (c.k - 1) h hw hw' hl (by omega) (by omega)
      (Or.inr htop) hY
    have hx : 0 < 1 / (c.a - c.v 1) := one_div_pos.mpr hapos
    have e : 8 / (c.a - c.v 1) = 8 * (1 / (c.a - c.v 1)) := by ring
    calc c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ (1 / (c.a - c.v 1)) * 1 :=
          mul_le_mul hU1 hr1 hr0 hx.le
      _ ≤ 8 / (c.a - c.v 1) := by rw [e]; linarith
  · obtain ⟨hbp1, _⟩ := h.htop htop
    have hb1 : (1:ℝ) ≤ c.b 1 := h.hb1
    have hbp : 0 < c.bp := by linarith
    have hk0 : (c.k:ℝ) ≠ 0 := (by linarith : (0:ℝ) < c.k).ne'
    have hD0 : c.Del ≠ 0 := (by linarith : (0:ℝ) < c.Del).ne'
    have hkD : 0 < (c.k:ℝ) * c.Del := mul_pos (by linarith) (by linarith)
    have haeff : c.aeff = c.a * c.bp / (c.k * c.Del) := by simp [Cfg.aeff, htop]
    rw [haeff]
    refine ⟨div_pos (mul_pos hapos' hbp) hkD, ?_⟩
    have hr1 := positionTop c de de' Y l h htop hl hlk hY
    have ha0 := hapos'.ne'
    have hb0 := hbp.ne'
    calc c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ (2 / c.a) * (4 * c.k * c.Del / c.bp) :=
          mul_le_mul (hU1.trans hU2) hr1 hr0 (div_nonneg (by norm_num) hapos'.le)
      _ = 8 / (c.a * c.bp / (c.k * c.Del)) := by
          field_simp
          ring

lemma prod_split (f : ℕ → ℝ) (k l : ℕ) (hl : 1 ≤ l) (hlk : l + 2 ≤ k) :
    ∏ i ∈ Icc 1 (k - 1), f i =
      (∏ i ∈ Ico 1 l, f i) * (f l * ((∏ i ∈ Ico (l + 1) (k - 1), f i) * f (k - 1))) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have e1 : n + 1 - 1 = n := by omega
  rw [e1]
  have e2 : Icc 1 n = Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e2, ← Finset.prod_Ico_consecutive f hl (by omega : l ≤ n + 1),
    Finset.prod_eq_prod_Ico_succ_bot (by omega : l < n + 1),
    Finset.prod_Ico_succ_top (by omega : l + 1 ≤ n)]

theorem betaOnCut_of_tcritLower (HT : TcritLower) : BetaOnCut := by
  intro c r bb de de' ka rd g VV T T' Y l h hm hs hw hw' hrd hka hg hFD hT hT' hl hlk hne hY
  have hka0 : 0 < ka := by rw [hka]; exact div_pos (by positivity) (by linarith)
  have hg0 : 0 < g := by linarith [Real.pi_pos]
  have hA : 0 < (ka ^ (c.m - 1))⁻¹ := inv_pos.mpr (pow_pos hka0 _)
  have hB : 0 < (Real.sqrt (T * T'))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hT hT'))
  have hgm : 0 < g ^ c.m := pow_pos hg0 _
  obtain ⟨haeff, hUR⟩ := edge_bound c de de' Y l h hw hw' hl hlk hY
  have hP := prodb_pos c h
  have hv0 := vthp_nonneg_of_ok c h
  have hcOne : 0 < cOne c bb := by
    unfold cOne
    exact div_pos (by positivity) (by linarith)
  have hfac := (betaFactorisation c de de' ka T T' Y l h hw hw' hT hT' hl hlk hne hY).2.2.2
  have hsplit := prod_split (c.rho de de' (-Y)) c.k l hl hlk
  have hR0 := positionsBefore c de de' Y l h hw hw' hl hlk hY
  have hRl := (slotAt_true c de de' Y l h hw hw' hl hlk hne hY).2
  have hN := nodeBound c Y l h hl hlk hY
  have hRm : ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i ≤ 1 :=
    Finset.prod_le_one (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
      (fun i hi => by
        rw [Finset.mem_Ico] at hi
        exact positionAfter c de de' Y l i h hw hw' hl (by omega) (by omega)
          (Or.inl (by omega)) hY)
  have hR00 : 0 ≤ ∏ i ∈ Ico 1 l, c.rho de de' (-Y) i :=
    Finset.prod_nonneg (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
  have hRm0 : 0 ≤ ∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i :=
    Finset.prod_nonneg (fun i _ => rho_nonneg c de de' Y l i h hlk hY)
  have hRl0 := rho_nonneg c de de' Y l l h hlk hY
  have hRk0 := rho_nonneg c de de' Y l (c.k - 1) h hlk hY
  have hN0 : 0 ≤ c.Nd (-Y) := by
    unfold Cfg.Nd
    exact Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _)
  have hU0 : 0 < c.U1 (-Y) := (edgeFactorBound c Y l h hl hlk hY).1
  have hsq : Real.sqrt (14 * (c.v l + Y) / (5 * c.Del)) =
      Real.sqrt (14 / 5) * Real.sqrt ((c.v l + Y) / c.Del) := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ 14 / 5 by norm_num) ((c.v l + Y) / c.Del)]
    congr 1
    ring
  rw [hsq] at hRl
  have hT1 := HT c r bb de ka rd g VV h hm hs hw hrd hka hg hFD
  have hT2 := HT c r bb de' ka rd g VV h hm hs hw' hrd hka hg hFD
  have hQ0 : 0 < cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff :=
    div_pos (mul_pos (mul_pos (mul_pos hcOne hgm) hA) hP) haeff
  have htv : cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff *
      (Real.sqrt (T * T'))⁻¹ ≤ tv c de de' ka rd g VV T T' := by
    unfold tv
    rw [Real.le_sqrt' (mul_pos hQ0 hB), mul_pow, inv_pow, Real.sq_sqrt (mul_pos hT hT').le,
      div_eq_mul_inv (Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de)) *
        Tcrit c.k c.m ka rd g VV (Vand c.k (c.u de')))]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (mul_pos hT hT').le)
    rw [pow_two]
    exact mul_le_mul hT1 hT2 hQ0.le (hQ0.le.trans hT1)
  have hEP : 0 < Real.exp c.vth * c.prodb := mul_pos (Real.exp_pos _) hP
  have hsk : 0 ≤ Real.sqrt c.k := Real.sqrt_nonneg _
  have hsx : 0 ≤ Real.sqrt ((c.v l + Y) / c.Del) := Real.sqrt_nonneg _
  have hs5 : 0 ≤ Real.sqrt (14 / 5) := Real.sqrt_nonneg _
  have b1 := mul_le_mul hN hR0 hR00 hEP.le
  have b2 := mul_le_mul b1 hRl hRl0 (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk))
  have b3 := mul_le_mul b2 hRm hRm0
    (mul_nonneg (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk)) (mul_nonneg hs5 hsx))
  have b4 := mul_le_mul b3 hUR (mul_nonneg hU0.le hRk0)
    (mul_nonneg (mul_nonneg (mul_nonneg hEP.le (mul_nonneg (by norm_num) hsk))
      (mul_nonneg hs5 hsx)) (by norm_num))
  have hK : 0 ≤ g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ :=
    (mul_pos (mul_pos hgm hA) hB).le
  have hAZ : 0 ≤ 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb :=
    div_nonneg (by positivity) hcOne.le
  have hae := haeff.ne'
  have hco := hcOne.ne'
  rw [hfac, hsplit]
  calc g ^ c.m * ((ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ * c.Nd (-Y) * c.U1 (-Y) *
        ((∏ i ∈ Ico 1 l, c.rho de de' (-Y) i) * (c.rho de de' (-Y) l *
          ((∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i) * c.rho de de' (-Y) (c.k - 1)))))
      = g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ *
        (c.Nd (-Y) * (∏ i ∈ Ico 1 l, c.rho de de' (-Y) i) * c.rho de de' (-Y) l *
          (∏ i ∈ Ico (l + 1) (c.k - 1), c.rho de de' (-Y) i) *
          (c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1))) := by ring
    _ ≤ g ^ c.m * (ka ^ (c.m - 1))⁻¹ * (Real.sqrt (T * T'))⁻¹ *
        (Real.exp c.vth * c.prodb * (3.3 * Real.sqrt c.k) *
          (Real.sqrt (14 / 5) * Real.sqrt ((c.v l + Y) / c.Del)) * 1 * (8 / c.aeff)) :=
        mul_le_mul_of_nonneg_left b4 hK
    _ = 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb *
        (cOne c bb * g ^ c.m * (ka ^ (c.m - 1))⁻¹ * c.prodb / c.aeff * (Real.sqrt (T * T'))⁻¹) *
        Real.sqrt c.k * Real.sqrt ((c.v l + Y) / c.Del) := by
        field_simp
    _ ≤ 8 * 3.3 * Real.sqrt (14 / 5) * Real.exp c.vth / cOne c bb *
        tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt ((c.v l + Y) / c.Del) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htv hAZ) hsk) hsx
    _ = AZero c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k *
        Real.sqrt ((c.v l + Y) / c.Del) := rfl

end Formalism.FourierDecayAlt.P.Sz7

namespace Formalism.FourierDecayAlt.P

theorem a_zero_le_one_sixty : Formalism.FourierDecayAlt.Sz.AZeroBound := Sz7.aZeroBound

theorem beta_bound_on_boundary : Formalism.FourierDecayAlt.Sz.BetaOnCut := Sz7.betaOnCut_of_tcritLower critical_threshold_lower_bound

end Formalism.FourierDecayAlt.P
