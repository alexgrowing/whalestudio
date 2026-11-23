import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNineExplicitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeLogFormAbsLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDivisionL1Bound

set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHt.ShortPf

theorem budget_arith {f r l b PP T d ρ s : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (hP : (f * r * l) ^ 12 ≤ PP)
    (hd : 1 ≤ d) (hT : d ^ 2 * PP ≤ T) (hTb : T ≤ b) (hρ : 0 ≤ ρ) (hρ1 : d * ρ * PP ≤ 6 * r ^ 2) (hs : 0 ≤ s)
    (hs1 : T * s ≤ 8 * f * r * b) :
    ((f * r * l) ^ 3 * s + (f * r * l) ^ 5) * (6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ)) ≤ 693 * (f * b) := by
  have hrZ : r ≤ f * r * l := by
    calc r = 1 * r * 1 := by ring
      _ ≤ _ := by gcongr
  generalize f * r * l = Z at *
  have hZ : 1 ≤ Z := hr.trans hrZ
  have h7 : Z ^ 7 ≤ PP := (pow_le_pow_right₀ hZ (by norm_num)).trans hP
  have hP0 : 0 < PP := lt_of_lt_of_le (by positivity) h7
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hb0 : 0 < b := hT0.trans_le hTb
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have e : T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ) = 7 * d ^ 2 + 7 * T * (d * ρ) + 2 * T * ρ := by field_simp
  have hF : (6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ)) * PP ≤ 77 * (r ^ 2 * T) := by
    rw [e]
    have a1 : d ≤ d ^ 2 := le_self_pow₀ hd (by norm_num)
    have a2 : ρ ≤ d * ρ := le_mul_of_one_le_left hρ hd
    have a3 : 6 * d + 10 + (7 * d ^ 2 + 7 * T * (d * ρ) + 2 * T * ρ) ≤ 23 * d ^ 2 + 9 * T * (d * ρ) := by
      nlinarith [mul_le_mul_of_nonneg_left a2 hT0.le]
    have a4 := mul_le_mul_of_nonneg_right a3 hP0.le
    have a5 := mul_le_mul_of_nonneg_left hρ1 hT0.le
    have a6 : T ≤ r ^ 2 * T := le_mul_of_one_le_left hT0.le hr2
    nlinarith
  generalize 6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ) = F at hF ⊢
  refine le_of_mul_le_mul_right ?_ hP0
  have b1 : (Z ^ 3 * s + Z ^ 5) * (F * PP) ≤ (Z ^ 3 * s + Z ^ 5) * (77 * (r ^ 2 * T)) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  have b2 : Z ^ 3 * r ^ 2 * (T * s) ≤ Z ^ 3 * r ^ 2 * (8 * f * r * b) := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have b3 : Z ^ 3 * r ^ 3 ≤ PP := by
    calc Z ^ 3 * r ^ 3 ≤ Z ^ 3 * Z ^ 4 :=
          mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by linarith) hrZ 3).trans (pow_le_pow_right₀ hZ (by norm_num)))
            (by positivity)
      _ = Z ^ 7 := by ring
      _ ≤ _ := h7
  have b4 : Z ^ 5 * r ^ 2 ≤ PP := by
    calc Z ^ 5 * r ^ 2 ≤ Z ^ 5 * Z ^ 2 := by gcongr
      _ = Z ^ 7 := by ring
      _ ≤ _ := h7
  have b5 : Z ^ 3 * r ^ 3 * (f * b) ≤ PP * (f * b) := mul_le_mul_of_nonneg_right b3 (by positivity)
  have b6 : Z ^ 5 * r ^ 2 * T ≤ PP * (f * b) :=
    mul_le_mul b4 (hTb.trans (le_mul_of_one_le_left hb0.le hf)) hT0.le hP0.le
  nlinarith

theorem len_mul_l1_le {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (hW : W.Hyp) (hD : W.IsDiv) :
    (W.T : ℝ) * GlobalTheory.MeanTop.l1 W.u1 ≤ Fintype.card ι * (N * (2 * W.b)) := by
  refine (GlobalTheory.MeanTop.divided_weight_size _ _ W hW hD).1.trans ?_
  have h : ∑ τ, ∑ k, (|(W.u τ k : ℝ)| + W.c0 + 4 * N) ≤ ∑ _τ : ι, ∑ _k : Fin N, 2 * W.b :=
    Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.h5 τ k
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold GlobalTheory.MeanTop.l1
  linarith

theorem fieldSz_host {D : D7} {L : SizeData₂ D} {PP A M : ℝ} (h : HostNum D L PP A M) : fieldSz D.host.E ≤ 3 * L.sc.L := by
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast h.f8
  have hr : (2 : ℝ) ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by unfold Ranks.r; omega : 2 ≤ D.R.r)
  unfold fieldSz
  rw [h.deg]
  push_cast
  have a1 : Real.log (2 * (D.R.f : ℝ)) ≤ Real.log ((D.R.f : ℝ) * D.R.r) := Real.log_le_log (by linarith) (by nlinarith)
  have a2 : Real.log |(discr D.host.E : ℝ)| / (2 * (D.R.f : ℝ)) ≤ 2 * L.sc.L := by
    rw [div_le_iff₀ (by linarith)]
    linarith [h.disc]
  linarith [h.logfr.1]

theorem log_level {D : D7} {L : SizeData₂ D} {PP A M : ℝ} (h : HostNum D L PP A M) :
    Real.log ((D.host.g 0 * D.host.g 1 * 15 ^ expL L.sc.L : ℕ) : ℝ) ≤ 30 * L.sc.L := by
  have hL := h.big.2.1
  have g0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have g1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have l3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have a1 : (expL L.sc.L : ℝ) * Real.log 3 ≤ 3 * L.sc.L :=
    (le_div_iff₀ l3).1 (Nat.floor_le (div_nonneg (by linarith) l3.le))
  have a2 : Real.log 15 ≤ 3 * Real.log 3 := by
    have : Real.log ((3 : ℝ) ^ 3) = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have a3 := mul_le_mul_of_nonneg_left a2 (Nat.cast_nonneg (α := ℝ) (expL L.sc.L))
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul g0.ne' g1.ne', Real.log_pow]
  linarith [h.logg 0, h.logg 1]

section Point

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

set_option maxHeartbeats 800000 in

theorem weight_rows {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hq : Quo p i PP u1) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (∀ τ, Antitone (u1 τ)) ∧
    (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ u1 τ a - u1 τ b) ∧
    Real.log (∑ τ, ∑ k, |(u1 τ k : ℝ)|) ≤ 10 * L.sc.L ∧
    (((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 3 * (∑ τ, ∑ k, |(u1 τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 5) *
      (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ 693 * unitE p := by
  obtain ⟨h0, S, eta, -, -, -, -, hh, hH⟩ := hw.hyp hi
  have hW := hH u1
  have hD := (quo_iff p i PP h0 S eta u1).1 hq
  have m2 := D.R.two_le_m
  have k3 := D.R.m_add_three_le_k
  have f8 := h.f8
  have hL := h.big.2.1
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f8
  have hr : (2 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 2 ≤ D.R.r)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hcard : Fintype.card (Psi p.T.Q.H) = D.R.f := by rw [← hw.card, Nat.card_eq_fintype_card]
  have hDd : (1 : ℝ) ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
  have hT : (1 : ℝ) ≤ lenT p i PP := by
    have : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hP : ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 12 ≤ PP := h.ppLow
  have hZ : (160 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * L.sc.L := by
    calc (160 : ℝ) = 8 * 2 * 10 := by norm_num
      _ ≤ _ := by gcongr
  have hP1 : 160 ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hP)
  have kp : (wtsAt p i PP h0 S eta u1).kc < (dat p i).p := hW.kc_lt
  have pq : (dat p i).p < (dat p i).p + (dat p i).q := hW.p_lt
  have s0 : 0 ≤ ∑ τ, ∑ k, |(u1 τ k : ℝ)| := by positivity
  have s1 : (lenT p i PP : ℝ) * ∑ τ, ∑ k, |(u1 τ k : ℝ)| ≤ 8 * D.R.f * D.R.r * L.sc.b := by
    have := len_mul_l1_le _ hW hD
    rw [hcard, show (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r by rw [hw.sig.2.2]] at this
    refine le_trans this (le_of_eq ?_)
    show (D.R.f : ℝ) * (D.R.r * (2 * (4 * L.sc.b))) = _
    ring
  have h1 : PP * lenT p i PP * D.R.r * D.R.f * dimFlag (dat p i) ≤ h0 := by
    refine le_trans ?_ hh
    have a1 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have a2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := one_le_pow₀ hm
    calc _ = PP * lenT p i PP * D.R.r * D.R.f * 1 * 1 * dimFlag (dat p i) := by ring
      _ ≤ _ := by gcongr; linarith
  refine ⟨by omega, by omega, fun τ => (GlobalTheory.MeanTop.divided_strictAnti _ _ _ hW hD τ).1.antitone, fun τ a b hab hb' => ?_, ?_, ?_⟩
  · have g : h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) := ((GlobalTheory.MeanTop.divided_gaps _ _ _ hW hD τ a b hab).2.1 hb').1
    have g' : (h0 : ℝ) ≤ 2 * (lenT p i PP : ℝ) * ((u1 τ a : ℝ) - u1 τ b) := by exact_mod_cast g
    have a1 : 160 * lenT p i PP * D.R.r * D.R.f * 1 ≤ PP * lenT p i PP * D.R.r * D.R.f * dimFlag (dat p i) := by gcongr
    have a2 : 80 * ((D.R.f : ℝ) * D.R.r) ≤ (u1 τ a : ℝ) - u1 τ b := by
      refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 2 * lenT p i PP by linarith)
      linarith
    have a3 : (16 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    have a4 : 8 * (D.R.f : ℝ) * D.R.r + 10 ≤ (u1 τ a : ℝ) - u1 τ b := by linarith
    exact_mod_cast a4
  · rcases s0.eq_or_lt with e | e
    · rw [← e, Real.log_zero]; linarith
    have a1 := Real.log_le_log e ((le_mul_of_one_le_left s0 hT).trans s1)
    rw [mul_assoc 8, Real.log_mul (by positivity) hb.ne', Real.log_mul (by norm_num) (by positivity),
      show Real.log L.sc.b = L.sc.L from Real.log_exp _] at a1
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num), h.logfr.1]
  · obtain ⟨r0, -, r2⟩ := GlobalTheory.CovTop.SizeRows.rho_bounds _ hW hD
    have er : rhoOf (wtsAt p i PP h0 S eta u1).u' (wtsAt p i PP h0 S eta u1).u1 = rhoB (dat p i) u1 := by
      unfold rhoB
      congr 1
      funext τ k
      rw [uPrime_apply]; rfl
    rw [er] at r0 r2
    have r3 : rhoB (dat p i) u1 * h0 ≤ 6 * D.R.f * (D.R.r : ℝ) ^ 3 * lenT p i PP := by
      rw [← hcard, ← hw.sig.2.2]; exact r2
    have r4 : dimFlag (dat p i) * rhoB (dat p i) u1 * PP ≤ 6 * (D.R.r : ℝ) ^ 2 := by
      refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < D.R.f * D.R.r * lenT p i PP by positivity)
      linarith [mul_le_mul_of_nonneg_left h1 r0]
    have hTl : (dimFlag (dat p i) : ℝ) ^ 2 * PP ≤ lenT p i PP := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ (by linarith), mul_comm _ PP]
      have : PP ≤ PP ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
      gcongr
    have hTb : (lenT p i PP : ℝ) ≤ L.sc.b := by
      refine le_trans ?_ hw.what₂.2
      have a2 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := one_le_pow₀ hDd
      calc (lenT p i PP : ℝ) = 1 * lenT p i PP * 1 * 1 := by ring
        _ ≤ _ := by gcongr <;> linarith
    refine (budget_arith (by linarith) (by linarith) (by linarith) hP hDd hTl hTb r0 r4 s0 s1).trans ?_
    rw [hw.unit]
    have hll := h.big.2.2.2
    calc 693 * ((D.R.f : ℝ) * L.sc.b) = 693 * (D.R.f * 1 * L.sc.b * 1 * 1) := by ring
      _ ≤ _ := by gcongr; linarith

end Point

set_option maxHeartbeats 800000 in

theorem short : Hypotheses2 → DeepGood → Size → FlatDeg → Short := fun hP _ _ hF => by
  obtain ⟨C, hC, H3⟩ := GlobalTheory.T.flat_constant_abs_le_nine_explicit hP
  refine Closed.imp (Closed.and (Closed.and (Sizes.hostN 1) WtShape.wtN) hF) fun Fm _ _ h => ?_
  obtain ⟨⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩, ⟨_, _, h3⟩⟩ := h
  obtain ⟨x0, h⟩ := (h1.and h2).and h3
  refine ⟨C * 693, by positivity, x0, fun x hx hle ι p hp i hi Y hY u1 hq => ?_⟩
  obtain ⟨⟨g1, g2⟩, g3⟩ := h x hx hle ι p hp
  have hH := g1 i
  have hw := g2 i
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := weight_rows p i hH hw hi u1 hq
  have hL := hH.big.2.1
  have hM : Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L := by
    rw [hY.1.lev.1.2.1, hY.1.pd, p.fw.laws.pins.2.1.1]
    exact log_level hH
  have key := H3 _ p.T p.fw.laws _ a1 a2 (by rw [hH.deg]; have := hH.f8; omega) ⟨by omega, hi.le⟩ Y _ _ hY.1 _ (by linarith) hM
    (fieldSz_host hH) hH.logfr.1 le_rfl _ (g3 i hi Y hY) (by rw [abs_neg]; exact FlatSz.abs_flatDegVal_le p i hH hw) u1 a3
    (fun τ => by
      unfold GlobalTheory.CompHS.gap
      rw [dif_pos (by show (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q; omega)]
      exact a4 τ _ _ rfl (by show (dat p i).p - 1 + 1 = _; omega)) a5
  refine ⟨Real.exp (C * ((((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 * (∑ τ, ∑ k, |(u1 τ k : ℝ)|) +
    (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 5)), fun Z => ?_, ?_⟩
  · obtain ⟨n, w, abelian₂, hs, hl, -⟩ := key Z
    have := (Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos hs.one_le)).1 hl
    exact ⟨n, w, hs.gen, fun k σ => (hs.le k σ).trans this, hs.one_le.trans this⟩
  · rw [Real.log_exp, mul_assoc, mul_assoc C]
    exact mul_le_mul_of_nonneg_left a6 hC

end GlobalTheory.CovHt.ShortPf
