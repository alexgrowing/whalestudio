import Formalism.LocalToGlobal.GlobalTheory.SmallShareWeightExists
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
import Formalism.LocalToGlobal.GlobalTheory.PowFourLtCeilThresholdPrime
import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss7

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds Formalism.LFunctionChainParameters.SmallOrderPrimeLosses Formalism.L2.GlobalTheoryTheory.Loss

section AtRecord

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts)

theorem cands_eq : cands L K = sAt L K := rfl

theorem card_lifts (D : D7) : (SizeData₂.lifts D).card = D.R.m := by
  simp [SizeData₂.lifts]

theorem card_TTv (D : D7) : (TTv D).card = D.host.TT.card := by
  have h := pb_sum_TTv (D := D) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe] at h
  exact_mod_cast h

open Classical in

theorem bad_card_at (p : ℕ) : ((TTv D).filter (fun n => badAt X p n)).card = (badTops X p).card := by
  have h := pb_sum_TTv (D := D) (fun n => if badAt X p n then (1 : ℝ) else 0)
  rw [Finset.sum_boole] at h
  have h2 : (∑ t : D.host.TT, if badAt X p (t : D.R.A).val then (1 : ℝ) else 0) = ((badTops X p).card : ℝ) := by
    rw [badTops, Finset.card_filter]
    push_cast
    rw [← Finset.sum_coe_sort D.host.TT]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [badAt, pb_cast]
  exact_mod_cast h.trans h2

end AtRecord

theorem loss_setting_family : LossSettingFamily := by
  classical
  intro D L X K Cr C bo P H hG tie hbo hLa hp0 hTT hB hW
  obtain ⟨-, -, -, -, -, -, -, ea, -, eθ⟩ := side_at X K Cr C bo H P tie hbo hLa hp0
  have hx0 : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hSig : ∀ p, 0 ≤ G.Sig X K (G.aL L) (G.bL L) p :=
    fun p => Lnk.Sig_nonneg X K H.Knn H.kapI _ _ p
  refine ⟨?_, ?_, fun p _ => hSig p, ?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · unfold TTv; exact hTT.image _
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_PsAt hp
    exact ⟨h1, fun h => two_not_inert _ (h ▸ h2)⟩
  · unfold ChW_at at hW
    unfold lhsW
    rw [eθ, tie.x, ← cands_eq]
    have e9 : L.sc.x ^ (-9 : ℝ) = (L.sc.x ^ 9)⁻¹ := by
      rw [Real.rpow_neg hx0.le]
      congr 1
      exact_mod_cast Real.rpow_natCast L.sc.x 9
    rw [← e9]
    exact hW
  · unfold ChBadp_at at hB
    unfold badPrimeLogWeightedCount
    rw [card_TTv, tie.x, tie.ε]
    simp only [bad_card_at]
    exact hB
  · intro _ p _
    have h := Lnk.ioP_le X K p (hG.2.1 p) (hSig p)
    rw [card_lifts, card_TTv, ea]
    exact h
  · exact lossHyp_at X K Cr C bo H hG P tie hbo hLa hp0
  · exact firstHyp_at X K Cr C bo H (T_not_inert _) P tie
  · intro p _ h
    obtain ⟨h1, h2⟩ := second_spec X K p h
    rw [eθ]
    exact ⟨(mem_sAt K).mpr h1, h2⟩
  · intro p hp h n hn
    have hn' : n ∈ TTv D ∧ n ∉ (ldAt X K C bo).TTp p := by
      simpa only [Finset.mem_sdiff] using hn
    exact unserved_bad X K Cr C bo H (T_not_inert _) p hp h n (Finset.mem_sdiff.mpr hn')

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem losses_of_small_share_weight (hTT : ChosenTT Fm) (hBad : ChosenBadp Fm) (hG : LinkG Fm) : Lnk.LossesSmallShares Fm := by
  classical
  obtain ⟨Cord, hCord, hJ⟩ := joint_discriminant_eventually
  obtain ⟨xT, hTT⟩ := hTT
  obtain ⟨xB, hBad⟩ := hBad
  obtain ⟨C, xG, δ, hδ, hG⟩ := hG
  obtain ⟨xA, hAsk⟩ := Lnk.askIsF Fm
  obtain ⟨e, K, x0, hW⟩ := windows_ev Fm C 0 Cord hCord δ hδ
  have heps : 0 < eps := Lnk.fam_eps_pos Fm
  have heps4 : eps < 1 / 4 := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_lt
    rw [Fm.L_eps 0 i] at this
    linarith
  obtain ⟨x1, hJ'⟩ := hJ eps e K heps heps4
  refine ⟨3 * |K| + 13, max (max x0 xT) (max xB (max xG (max xA x1))), by positivity, fun x hxx i hWi => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxx
  have eT : x ≥ xT := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxx
  have eB : x ≥ xB := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxx
  have eG : x ≥ xG := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hxx
  have eA : x ≥ xA := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)) hxx
  have e1 : x1 ≤ x := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)) hxx
  obtain ⟨hx, h3, hW⟩ := hW x e0
  obtain ⟨hW, hp0⟩ := hW i
  set bo : ℝ := (Fm.L x i).sc.b ^ δ x with hbo
  have hbo0 : 0 ≤ bo := Real.rpow_nonneg (Real.exp_pos _).le _
  set P : Par := par Fm x i C bo 0 Cord with hP
  have tie : ParTie P (Fm.L x i) Fm.GK C bo Fm.Cr := parTie (i0 := i) hx i C bo 0 Cord
  have hH : PtH (Fm.Gx x i) Fm.GK Fm.Cr := ptH Fm hx h3 i
  have hLa : 0 ≤ (Fm.L x i).LaG := by
    have h1 := (Fm.sizes x hx i).2.2.2.2.2.2.2.2.1.1
    exact le_trans (Real.rpow_nonneg (lt_trans one_pos (Fm.L x i).sc.one_lt_alt).le _) h1
  have hne : (Fm.D x i).host.TT.Nonempty := by
    rw [← Finset.card_pos]
    have h1 := (hTT x eT i).1
    have hx0 : 0 < (Fm.L x i).sc.x := lt_trans one_pos (Fm.L x i).sc.one_lt_alt
    have h2 : 0 < (Fm.L x i).sc.delta1 * (Fm.D x i).R.n / 2 := by
      have : 0 < (Fm.L x i).sc.delta1 := Real.rpow_pos_of_pos hx0 _
      have h4 : (0 : ℝ) < (Fm.D x i).R.n := lt_of_lt_of_le one_pos (Lnk.one_le_n _)
      positivity
    exact_mod_cast lt_of_lt_of_le h2 h1
  have hS := loss_setting_family (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK Fm.Cr C bo P hH (hG x eG i) tie hbo0 hLa hp0 hne
    (hBad x eB i) hWi
  have hPx : P.x = x := Fm.L_x x i hx
  have hPe : P.ε = eps := Fm.L_eps x i
  obtain ⟨hc1, hc2⟩ := hJ' P hPe rfl (by rw [hPx]; exact e1) (discriminant_windows_of P e K hW) ℕ ℕ ℕ Unit _ _ _ _ _ _ _ _ _ hS
  have hPC0 : 0 ≤ P.C := le_max_right _ _
  have hPCK : P.C ≤ K := hW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hU : unitU P (SizeData₂.lifts (Fm.D x i)).card (TTv (Fm.D x i)).card =
      ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b := by
    unfold unitU; rw [card_lifts, card_TTv, pd_b tie]
  have hU0 : 0 ≤ ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hone : (Fm.L x i).sc.x ^ ((0 : ℝ) * (Fm.L x i).sc.eps) = 1 := by rw [zero_mul, Real.rpow_zero]
  have hKabs : K ≤ |K| := le_abs_self K
  have hbig : (3 * P.C + 13) * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) ≤
      (3 * |K| + 13) * (Fm.D x i).host.TT.card * (Fm.D x i).R.m * (Fm.L x i).sc.b *
        (Fm.L x i).sc.x ^ ((0 : ℝ) * (Fm.L x i).sc.eps) := by
    rw [hone, mul_one]
    have := mul_le_mul_of_nonneg_right (show 3 * P.C + 13 ≤ 3 * |K| + 13 by linarith) hU0
    simpa [mul_assoc] using this
  have hsmall : ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b ≤
      (3 * P.C + 13) * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 * P.C + 13 by linarith) hU0
    linarith
  constructor
  · have h2 := hc2 ()
    rw [IO_at (Fm.Gx x i) Fm.GK Fm.Cr hH, hU] at h2
    linarith
  · intro e' m' AD N TT' a w hr hAD hcut
    rw [hAsk x eA i e' m' AD N TT' a w hr hAD hcut]
    have h1 := hc1 ()
    rw [Ga_at (Fm.Gx x i) Fm.GK Fm.Cr C bo hH, hU, tie.d, ASK_at (Fm.Gx x i) Fm.GK Fm.Cr C bo hH] at h1
    linarith

end Family

theorem stLoss7 : ThickDensitySizeWindowsForAllFamilies := fun _ Fm h1 h2 h3 => losses_of_small_share_weight Fm h1 h2 h3

theorem stLoss7W : StLoss7W := fun _ Fm h1 h2 hW h3 => Lnk.lossF_of_7W Fm (losses_of_small_share_weight Fm h1 h2 h3) hW

section Size

variable {D : D7} {L : SizeData₂ D}

theorem size_alt_alt (sN : SizeN L) (sM : SizeM L) (sTT : SizeTT L) (h24 : 24 ≤ L.sc.x ^ ((1 : ℝ) / 4)) :
    (2 / L.sc.x ^ (-L.sc.eps) + 4) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ)) *
      (2 * L.sc.x ^ (L.sc.eps / 3)) ≤ L.sc.x ^ (-9 : ℝ) := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have hδ : L.sc.delta1 = L.sc.x ^ (-(L.sc.eps / 8)) := rfl
  have hA : 2 / L.sc.x ^ (-L.sc.eps) + 4 ≤ 6 * L.sc.x ^ L.sc.eps := by
    rw [Real.rpow_neg hx0.le, div_inv_eq_mul]
    have : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1.le he0.le
    linarith
  have hm : (D.R.m : ℝ) ≤ L.sc.x ^ (L.sc.eps / 100 + (1 - L.sc.eps / 8) / 2) := by
    have h := sM.2
    unfold szTh at h
    rw [hδ] at h
    have hs : Real.sqrt (L.sc.x * L.sc.x ^ (-(L.sc.eps / 8))) = L.sc.x ^ ((1 - L.sc.eps / 8) / 2) := by
      rw [Real.sqrt_eq_rpow, show L.sc.x * L.sc.x ^ (-(L.sc.eps / 8)) = L.sc.x ^ (1 - L.sc.eps / 8) by
        rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one], ← Real.rpow_mul hx0.le]
      congr 1
      ring
    rw [hs, ← Real.rpow_add hx0] at h
    exact h
  have hT : (D.host.TT.card : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 8)) := by
    have h1 := sTT.2
    have h2 := sN.2
    unfold szNst at h1
    unfold szTh at h2
    rw [hδ] at h1
    calc _ ≤ _ := h1
      _ ≤ _ := by gcongr
  have hprod : L.sc.x ^ L.sc.eps * L.sc.x ^ (L.sc.eps / 100 + (1 - L.sc.eps / 8) / 2) *
      L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 8)) * L.sc.x ^ (-12 : ℝ) *
      L.sc.x ^ (L.sc.eps / 3) =
      L.sc.x ^ (L.sc.eps + (L.sc.eps / 100 + (1 - L.sc.eps / 8) / 2) + (2 + 8 * L.sc.eps + L.sc.eps / 100) +
        -(L.sc.eps / 8) + (-12 : ℝ) + L.sc.eps / 3) := by
    simp only [Real.rpow_add hx0]
  have hexp : (1 / 4 : ℝ) + (L.sc.eps + (L.sc.eps / 100 + (1 - L.sc.eps / 8) / 2) + (2 + 8 * L.sc.eps + L.sc.eps / 100) +
      -(L.sc.eps / 8) + (-12 : ℝ) + L.sc.eps / 3) ≤ -9 := by linarith
  calc (2 / L.sc.x ^ (-L.sc.eps) + 4) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.x ^ (-12 : ℝ)) *
        (2 * L.sc.x ^ (L.sc.eps / 3))
      ≤ (6 * L.sc.x ^ L.sc.eps) * (L.sc.x ^ (L.sc.eps / 100 + (1 - L.sc.eps / 8) / 2) *
          (2 * L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 8))) * L.sc.x ^ (-12 : ℝ)) *
        (2 * L.sc.x ^ (L.sc.eps / 3)) := by gcongr
    _ = 24 * (L.sc.x ^ L.sc.eps * L.sc.x ^ (L.sc.eps / 100 + (1 - L.sc.eps / 8) / 2) *
      L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 8)) * L.sc.x ^ (-12 : ℝ) *
      L.sc.x ^ (L.sc.eps / 3)) := by ring
    _ ≤ L.sc.x ^ ((1 : ℝ) / 4) * (L.sc.x ^ L.sc.eps * L.sc.x ^ (L.sc.eps / 100 + (1 - L.sc.eps / 8) / 2) *
      L.sc.x ^ (2 + 8 * L.sc.eps + L.sc.eps / 100) * L.sc.x ^ (-(L.sc.eps / 8)) * L.sc.x ^ (-12 : ℝ) *
      L.sc.x ^ (L.sc.eps / 3)) := by gcongr
    _ = L.sc.x ^ ((1 : ℝ) / 4 + (L.sc.eps + (L.sc.eps / 100 + (1 - L.sc.eps / 8) / 2) +
        (2 + 8 * L.sc.eps + L.sc.eps / 100) + -(L.sc.eps / 8) + (-12 : ℝ) + L.sc.eps / 3)) := by
      rw [hprod, ← Real.rpow_add hx0]
    _ ≤ L.sc.x ^ (-9 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le hexp

end Size

theorem exists_le_of_sum {Ω : Type} [Fintype Ω] [Nonempty Ω] (F : Ω → ℝ) (B : ℝ)
    (h : ∑ o, F o ≤ (Fintype.card Ω : ℝ) * B) : ∃ o, F o ≤ B := by
  by_contra hc
  push_neg at hc
  have h2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun o _ => hc o)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  linarith

theorem term_le (θ s : ℝ) (hθ : 0 < θ) (hs : 0 ≤ s) : ((if θ < s then 2 else 0) + 4 * s : ℝ) ≤ (2 / θ + 4) * s := by
  split_ifs with h
  · have h2 : 2 ≤ 2 / θ * s := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
      linarith
    rw [add_mul]
    linarith
  · have h2 : 0 ≤ 2 / θ * s := by positivity
    rw [add_mul]
    linarith

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem chosenW_of (hG : LinkG Fm) : ChosenW Fm := by
  obtain ⟨C, xG, δ, -, hG⟩ := hG
  obtain ⟨a24, -, h24⟩ := Lnk.ev_le_rpow ((1 : ℝ) / 4) (by norm_num) 24
  refine ⟨max (Fm.x1 + 1) (max xG a24), fun x hxx hxWin => ?_⟩
  have hx : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hxx
    linarith
  have eG : x ≥ xG := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxx
  have e24 : x ≥ a24 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hxx
  obtain ⟨i0⟩ := Fm.Ix_win x hxWin
  have h4 : G.MeanKappaBound (Fm.Gx x i0) Fm.GK := (hG x eG i0).2.2.2.2
  have := Lnk.wt_nonempty (i0 := i0) hx
  have hsx := Fm.L_x x i0 hx
  have hx0 : 0 < (Fm.L x i0).sc.x := lt_trans one_pos (Fm.L x i0).sc.one_lt_alt
  have hcard : (0 : ℝ) < (Fintype.card (Lnk.Wt Fm x i0) : ℝ) := by exact_mod_cast Fintype.card_pos
  set θ : ℝ := (Fm.L x i0).sc.x ^ (-(Fm.L x i0).sc.eps) with hθ
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos hx0 _
  set s0 : ℝ := ((Fm.D x i0).R.m : ℝ) * ((Fm.D x i0).host.TT.card : ℝ) * (Fm.L x i0).sc.x ^ (-12 : ℝ) with hs0
  have hs00 : 0 ≤ s0 := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.rpow_nonneg hx0.le _)
  have hA0 : 0 ≤ 2 / θ + 4 := by
    have : 0 ≤ 2 / θ := div_nonneg (by norm_num) hθ0.le
    linarith
  have hSig : ∀ p (o : Lnk.Wt Fm x i0), 0 ≤ SigO p o := fun p o =>
    Lnk.Sig_nonneg (Fm.Gx x i0) Fm.GK Fm.GK_nonneg (Fm.ex x hx i0).kapI_def _ _ p
  have hlp : ∀ p : ℕ, 0 ≤ Real.log (p : ℝ) / p := fun p => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

  have hX' : (Fm.L x i0).sc.X' = Real.exp ((Fm.L x i0).sc.x ^ ((Fm.L x i0).sc.eps / 3)) := rfl
  have hM : ∑ p ∈ sAt (Fm.L x i0) Fm.GK, Real.log (p : ℝ) / p ≤ 2 * (Fm.L x i0).sc.x ^ ((Fm.L x i0).sc.eps / 3) := by
    have h1 := Formalism.L2.GlobalTheoryTheory.Places.mertens (Fm.L x i0).sc.X' (pd_one_le_X' _)
    rw [hX', Real.log_exp, ← hX'] at h1
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hlp p)) h1
    intro p hp
    have hc := (mem_sAt Fm.GK).mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hc.2.1), hc.1⟩

  have hsum : ∑ o : Lnk.Wt Fm x i0, lhsW (sAt (Fm.L x i0) Fm.GK) θ (fun p => SigO p o) ≤
      (Fintype.card (Lnk.Wt Fm x i0) : ℝ) *
        ((2 / θ + 4) * s0 * (2 * (Fm.L x i0).sc.x ^ ((Fm.L x i0).sc.eps / 3))) := by
    have t1 : ∑ o : Lnk.Wt Fm x i0, lhsW (sAt (Fm.L x i0) Fm.GK) θ (fun p => SigO p o) ≤
        ∑ o : Lnk.Wt Fm x i0, ∑ p ∈ sAt (Fm.L x i0) Fm.GK, Real.log (p : ℝ) / p * ((2 / θ + 4) * SigO p o) := by
      refine Finset.sum_le_sum fun o _ => ?_
      unfold lhsW
      exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (term_le θ _ hθ0 (hSig p o)) (hlp p)
    have t2 : ∑ o : Lnk.Wt Fm x i0, ∑ p ∈ sAt (Fm.L x i0) Fm.GK, Real.log (p : ℝ) / p * ((2 / θ + 4) * SigO p o) =
        ∑ p ∈ sAt (Fm.L x i0) Fm.GK, Real.log (p : ℝ) / p * ((2 / θ + 4) * ∑ o : Lnk.Wt Fm x i0, SigO p o) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
    have t3 : ∑ p ∈ sAt (Fm.L x i0) Fm.GK, Real.log (p : ℝ) / p * ((2 / θ + 4) * ∑ o : Lnk.Wt Fm x i0, SigO p o) ≤
        ∑ p ∈ sAt (Fm.L x i0) Fm.GK, Real.log (p : ℝ) / p *
          ((2 / θ + 4) * (s0 * (Fintype.card (Lnk.Wt Fm x i0) : ℝ))) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hmean := mean_SigO hx h4 p ((mem_sAt Fm.GK).mp hp)
      rw [div_le_iff₀ hcard] at hmean
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmean hA0) (hlp p)
    have t4 : ∑ p ∈ sAt (Fm.L x i0) Fm.GK, Real.log (p : ℝ) / p *
          ((2 / θ + 4) * (s0 * (Fintype.card (Lnk.Wt Fm x i0) : ℝ))) =
        ((2 / θ + 4) * (s0 * (Fintype.card (Lnk.Wt Fm x i0) : ℝ))) * ∑ p ∈ sAt (Fm.L x i0) Fm.GK, Real.log (p : ℝ) / p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    have t5 := mul_le_mul_of_nonneg_left hM
      (show 0 ≤ (2 / θ + 4) * (s0 * (Fintype.card (Lnk.Wt Fm x i0) : ℝ)) from
        mul_nonneg hA0 (mul_nonneg hs00 hcard.le))
    calc _ ≤ _ := t1
      _ = _ := t2
      _ ≤ _ := t3
      _ = _ := t4
      _ ≤ _ := t5
      _ = _ := by ring
  obtain ⟨o, ho⟩ := exists_le_of_sum _ _ hsum
  have hS := Fm.sizes x hx i0
  have hsize := size_alt_alt hS.1 hS.2.1 hS.2.2.2.2.2.2.2.1 (by rw [hsx]; exact h24 x e24)
  refine ⟨i0, Lnk.avOf o, Lnk.bvOf o, Lnk.admissible_weight_of_vector o, fun i hi => ?_⟩
  unfold ChW_at
  rw [cands_eq, sAt_eq (i0 := i0) hx i, Lnk.sc_eq Fm hx i i0]
  simp only [Sig_eq hx i o hi]
  exact le_trans ho hsize

theorem loss_requirements_of_local_input (C0 CH : ℝ) (h : ChosenE Fm C0 CH) (hG : LinkG Fm) (hc : Fm.CoverAll) :
    WeightVectorSmallSharesSeven Fm C0 CH := by
  obtain ⟨C5, c6, Cb, h5, h6, hb, hT2, hTT, hBad, hQD, hThin, hPr, hCode⟩ := h
  exact ⟨C5, c6, h5, h6, Lnk.thick_density_of_construction Fm hT2, hTT, Lnk.chosenBadp_of_old Fm Cb hb.le hTT hBad,
    chosenWS_of_cover (Fm := Fm) (chosenW_of Fm hG) hc, hQD, hThin, hPr, hCode⟩

theorem loss_requirements_of_small_shares (C0 CH : ℝ) (h : ChosenE Fm C0 CH) (hW : ChosenWall Fm) : WeightVectorSmallSharesSeven Fm C0 CH := by
  obtain ⟨C5, c6, Cb, h5, h6, hb, hT2, hTT, hBad, hQD, hThin, hPr, hCode⟩ := h
  exact ⟨C5, c6, h5, h6, Lnk.thick_density_of_construction Fm hT2, hTT, Lnk.chosenBadp_of_old Fm Cb hb.le hTT hBad,
    chosenWS_of_wall (Fm := Fm) hW, hQD, hThin, hPr, hCode⟩

end Family

theorem small_share_weight_exists : SmallShareWeightExists := fun _ Fm hG => chosenW_of Fm hG

theorem stOld7 : StOld7 := fun _ Fm C0 CH h hG hc => loss_requirements_of_local_input Fm C0 CH h hG hc

example {eps : ℝ} (Fm : FamP eps) : ChosenTT Fm → ChosenBadp Fm → LinkG Fm → Lnk.LossesSmallShares Fm := stLoss7 eps Fm

end Formalism.L2.GlobalTheoryTheory.Loss7

end
