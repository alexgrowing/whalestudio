import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.BDivXNonneg

noncomputable section

namespace PI.SzEatI.W

open Formalism.BasicNotions Formalism.MainNotions.G

section counts

variable {D : D7}

private theorem card_HH_lemma : Fintype.card (HH D) = D.R.n := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_fin _

theorem card_univ_eq : (Fintype.card (Bool × HH D) : ℝ) = (D.R.f : ℝ) := by
  rw [Fintype.card_prod, Fintype.card_bool, card_HH_lemma]
  norm_num [Formalism.BasicNotions.Ranks.f]

theorem card_kindBC_le (p : ℕ) : ((kindBC D p).card : ℝ) ≤ (D.R.f : ℝ) := by
  have h : (kindBC D p).card ≤ Fintype.card (Bool × HH D) := by
    exact (Finset.card_filter_le _ _).trans Finset.card_univ.le
  calc ((kindBC D p).card : ℝ) ≤ (Fintype.card (Bool × HH D) : ℝ) := by exact_mod_cast h
    _ = (D.R.f : ℝ) := card_univ_eq

theorem card_topsBC_le (p : ℕ) : ((topsBC D p).card : ℝ) ≤ (D.R.f : ℝ) := by
  have h : (topsBC D p).card ≤ (kindBC D p).card := by
    classical
    convert Finset.card_filter_le (kindBC D p) (fun z => IsTopPl D z)
    unfold Formalism.BasicNotions.topsBC
    congr
  have h' : ((topsBC D p).card : ℝ) ≤ ((kindBC D p).card : ℝ) := by exact_mod_cast h
  exact h'.trans (card_kindBC_le p)

theorem N_le_Nm (i : ℕ) (hi : i ≤ D.R.m) : (D.R.N i : ℝ) ≤ Nm D := by
  unfold Formalism.MainNotions.G.Nm
  have h : D.R.N i ≤ D.R.N D.R.m := by
    unfold Formalism.BasicNotions.Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  exact_mod_cast h

theorem one_le_Nm : (1 : ℝ) ≤ Nm D := by
  unfold Formalism.MainNotions.G.Nm
  have hk := D.R.m_add_three_le_k
  have h : 1 ≤ D.R.N D.R.m := by
    unfold Formalism.BasicNotions.Ranks.N
    exact le_add_right (by omega)
  exact_mod_cast h

theorem nP_le_nW (p : ℕ) : (nP D p : ℝ) ≤ 2 * (D.R.n : ℝ) := by
  have h : nP D p ≤ 2 * D.R.n := by
    unfold Formalism.MainNotions.G.nP
    split_ifs
    · have h1 := addOrderOf_le_card_univ (x := 2 • hP D p)
      rw [card_HH_lemma] at h1
      omega
    · have h1 := addOrderOf_le_card_univ (x := hP D p)
      rw [card_HH_lemma] at h1
      omega
  exact_mod_cast h

theorem gam_le (p : ℕ) (hp : 2 ≤ p) : gam p ≤ 2 / (p : ℝ) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold Formalism.MainNotions.G.gam
  have h1 : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
  have h2 : 0 < (p : ℝ) := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

theorem gam_nonneg (p : ℕ) (hp : 2 ≤ p) : 0 ≤ gam p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold Formalism.MainNotions.G.gam
  apply div_nonneg (by linarith)
  nlinarith

end counts

section sizes

variable {D : D7} (L : SizeData₂ D)

theorem eta_le_b (hSz : Formalism.MainNotions.SizesAt L) : L.etaSz ≤ L.sc.b := by
  have h := hSz
  unfold Formalism.MainNotions.SizesAt at h
  have hE := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Formalism.MainNotions.SizeEta at hE
  have h2 := hE.2.1
  have ht : (1 : ℝ) ≤ D.R.t := Nat.one_le_cast.mpr D.R.t_odd.pos
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact Nat.one_le_cast.mpr (by omega)
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h3 := D.R.m_le_f
    have h4 := D.R.two_le_m
    have : 1 ≤ D.R.f := by
      unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
      omega
    exact Nat.one_le_cast.mpr this
  have hden : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) hf)
      (one_le_pow₀ hk)
  have hb : 0 < L.sc.b := Real.exp_pos _
  exact h2.trans (div_le_self hb.le hden)

theorem Sc_le_b (hSz : Formalism.MainNotions.SizesAt L) (hbb : L.sc.b' ≤ L.sc.b) : L.Sc ≤ L.sc.b := by
  have h := hSz
  unfold Formalism.MainNotions.SizesAt at h
  have hD := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Formalism.MainNotions.SizeDel at hD
  have h4 : (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n := hD.2.2.2.1
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact Nat.one_le_cast.mpr (by omega)
  have hn : (1 : ℝ) ≤ D.R.n := by
    have h3 := D.R.m_le_f
    have h5 := D.R.two_le_m
    have : 1 ≤ D.R.n := by
      unfold Formalism.BasicNotions.Ranks.n
      omega
    exact Nat.one_le_cast.mpr this
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hSc : 0 < L.Sc := L.Sc_pos
  have hw : L.sc.w'' D.R.n = L.sc.b' / (L.sc.x * D.R.n) := rfl
  have hkS : L.Sc ≤ D.R.k * L.Sc := by nlinarith
  have hxn : 0 < L.sc.x * D.R.n := mul_pos (by linarith) (by linarith)
  have hw0 : 0 < L.sc.w'' D.R.n := by linarith
  have hb'0 : 0 < L.sc.b' := by
    rw [hw] at hw0
    exact (div_pos_iff_of_pos_right hxn).mp hw0
  have hw' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    rw [hw]
    exact div_le_self hb'0.le (one_le_mul_of_one_le_of_one_le hx.le hn)
  linarith

theorem one_le_a : 1 ≤ L.sc.a := by
  unfold Formalism.BasicNotions.Scale.a Formalism.BasicNotions.Scale.b
  have hx := L.sc.one_lt_alt
  have he : 1 ≤ Real.exp L.sc.L := by
    apply Real.one_le_exp
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_nonneg (by linarith) _
  nlinarith

end sizes

section real

theorem dec_real (lp M gm T B c6 s p C N1 N2 lY d1 Nm l d2 : ℝ) (hlp : lp ≠ 0) :
    lp * (M + gm * T * B + c6 * s / p + C * N1 * N2 * (lY / lp + 1) +
        (d1 * C * Nm ^ 2 * (l / lp) + d2 * T * (l / lp) ^ 2) - M) =
      lp * (gm * T * B) + lp * (c6 * s / p) + C * N1 * N2 * (lY + lp) +
        (d1 * C * Nm ^ 2 * l + d2 * T * l ^ 2 / lp) := by
  field_simp
  ring

theorem iv_real (d1 d2 C T f Nm l lp : ℝ) (hC : C ≤ f) (hT : T ≤ f) (hC0 : 0 ≤ C) (hT0 : 0 ≤ T)
    (hl : 0 ≤ l) (hlp : 1 / 2 ≤ lp) :
    d1 * C * Nm ^ 2 * l + d2 * T * l ^ 2 / lp ≤ f * (|d1| * Nm ^ 2 * l + 2 * |d2| * l ^ 2) := by
  have hlp0 : 0 < lp := by linarith
  have hf0 : 0 ≤ f := le_trans hC0 hC
  have hNl : 0 ≤ Nm ^ 2 * l := mul_nonneg (sq_nonneg _) hl
  have t1 : d1 * C * Nm ^ 2 * l ≤ f * (|d1| * Nm ^ 2 * l) := by
    have e1 : d1 * C * Nm ^ 2 * l = (d1 * C) * (Nm ^ 2 * l) := by ring
    have e2 : f * (|d1| * Nm ^ 2 * l) = (|d1| * f) * (Nm ^ 2 * l) := by ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_right _ hNl
    calc d1 * C ≤ |d1| * C := mul_le_mul_of_nonneg_right (le_abs_self _) hC0
      _ ≤ |d1| * f := mul_le_mul_of_nonneg_left hC (abs_nonneg _)
  have t2 : d2 * T * l ^ 2 / lp ≤ f * (2 * |d2| * l ^ 2) := by
    have hinv : 1 / lp ≤ 2 := (div_le_iff₀ hlp0).2 (by linarith)
    have hinv0 : 0 ≤ 1 / lp := (one_div_pos.2 hlp0).le
    have e1 : d2 * T * l ^ 2 / lp = (d2 * T * l ^ 2) * (1 / lp) := by ring
    rw [e1]
    have hA : d2 * T * l ^ 2 ≤ |d2| * f * l ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg l)
      calc d2 * T ≤ |d2| * T := mul_le_mul_of_nonneg_right (le_abs_self _) hT0
        _ ≤ |d2| * f := mul_le_mul_of_nonneg_left hT (abs_nonneg _)
    have hB : 0 ≤ |d2| * f * l ^ 2 := mul_nonneg (mul_nonneg (abs_nonneg _) hf0) (sq_nonneg _)
    calc (d2 * T * l ^ 2) * (1 / lp) ≤ (|d2| * f * l ^ 2) * (1 / lp) :=
          mul_le_mul_of_nonneg_right hA hinv0
      _ ≤ (|d2| * f * l ^ 2) * 2 := mul_le_mul_of_nonneg_left hinv hB
      _ = f * (2 * |d2| * l ^ 2) := by ring
  calc d1 * C * Nm ^ 2 * l + d2 * T * l ^ 2 / lp
      ≤ f * (|d1| * Nm ^ 2 * l) + f * (2 * |d2| * l ^ 2) := add_le_add t1 t2
    _ = f * (|d1| * Nm ^ 2 * l + 2 * |d2| * l ^ 2) := by ring

theorem i_real (lp gm T B p f b : ℝ) (hlp : 0 ≤ lp) (hp : 0 < p) (hg : gm ≤ 2 / p) (hg0 : 0 ≤ gm)
    (hT : T ≤ f) (hT0 : 0 ≤ T) (hB : B ≤ 6 * b) (hB0 : 0 ≤ B) :
    lp * (gm * T * B) ≤ 12 * f * b * (lp / p) := by
  have hf0 : 0 ≤ f := hT0.trans hT
  have h2p : 0 ≤ 2 / p := (div_pos two_pos hp).le
  have h1 : gm * T * B ≤ (2 / p) * f * (6 * b) :=
    mul_le_mul (mul_le_mul hg hT hT0 h2p) hB hB0 (mul_nonneg h2p hf0)
  calc lp * (gm * T * B) ≤ lp * ((2 / p) * f * (6 * b)) := mul_le_mul_of_nonneg_left h1 hlp
    _ = 12 * f * b * (lp / p) := by ring

theorem ii_real (lp c6 s p f b : ℝ) (hlp : 0 ≤ lp) (hp : 0 < p) (hs0 : 0 ≤ s) (hs : s ≤ f * (5 * b)) :
    lp * (c6 * s / p) ≤ 5 * |c6| * f * b * (lp / p) := by
  have h1 : c6 * s ≤ |c6| * (f * (5 * b)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hs0).trans
      (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
  have h2 : c6 * s / p ≤ |c6| * (f * (5 * b)) / p := div_le_div_of_nonneg_right h1 hp.le
  calc lp * (c6 * s / p) ≤ lp * (|c6| * (f * (5 * b)) / p) := mul_le_mul_of_nonneg_left h2 hlp
    _ = 5 * |c6| * f * b * (lp / p) := by ring

theorem iii_real (C N1 N2 f Nm lY lp l8 lX : ℝ) (hC : C ≤ f) (hC0 : 0 ≤ C) (hN1 : N1 ≤ Nm) (hN2 : N2 ≤ Nm)
    (hN10 : 0 ≤ N1) (hN20 : 0 ≤ N2) (hY : lY ≤ l8) (hp : lp ≤ lX) (hd0 : 0 ≤ l8 + lX) :
    C * N1 * N2 * (lY + lp) ≤ f * (Nm ^ 2 * (l8 + lX)) := by
  have hf0 : 0 ≤ f := hC0.trans hC
  have hP0 : 0 ≤ C * N1 * N2 := mul_nonneg (mul_nonneg hC0 hN10) hN20
  have hNm0 : 0 ≤ Nm := hN10.trans hN1
  have hP : C * N1 * N2 ≤ f * Nm ^ 2 := by
    calc C * N1 * N2 ≤ f * Nm * Nm :=
          mul_le_mul (mul_le_mul hC hN1 hN10 hf0) hN2 hN20 (mul_nonneg hf0 hNm0)
      _ = f * Nm ^ 2 := by ring
  calc C * N1 * N2 * (lY + lp) ≤ C * N1 * N2 * (l8 + lX) :=
        mul_le_mul_of_nonneg_left (by linarith) hP0
    _ ≤ f * Nm ^ 2 * (l8 + lX) := mul_le_mul_of_nonneg_right hP hd0
    _ = f * (Nm ^ 2 * (l8 + lX)) := by ring

end real

theorem prime_weighted_remainder_bound (K : Consts) (ce : ErrC) (D : D7) (L : SizeData₂ D) (hSz : Formalism.MainNotions.SizesAt L) (hbb : L.sc.b' ≤ L.sc.b)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (p : ℕ) (hp : p.Prime) (hpX : (p : ℝ) ≤ L.sc.X'' D.R.n) :
    Real.log p * (rest L K ce j p - EatX L ce j p) ≤
      c1 ce * (D.R.f : ℝ) * L.sc.b * (Real.log p / p) + (D.R.f : ℝ) * Rt L K := by
  have hj' := hj
  unfold SizeData₂.lifts at hj'
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj'
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hlp2 : (1 / 2 : ℝ) ≤ Real.log p := by have := Real.log_two_gt_d9; linarith
  have hlp0 : 0 < Real.log p := by linarith
  have hf0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hb := b_pos L
  have hb1 := one_le_b L
  have hη := eta_le_b L hSz
  have hη0 := L.etaSz_pos
  have hSc := Sc_le_b L hSz hbb
  have hSc0 := L.Sc_pos
  have hNm1 : (1 : ℝ) ≤ Nm D := one_le_Nm
  have ha1 := one_le_a L
  have hn1 : (1 : ℝ) ≤ (D.R.n : ℝ) := n_one_le
  have hdec : Real.log p * (rest L K ce j p - EatX L ce j p) =
      Real.log p * (gam p * ((topsBC D p).card : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc)) +
      Real.log p * (ce.c6 * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ)) +
      ((kindBC D p).card : ℝ) * (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) *
        (Real.log (4 * (nP D p : ℝ) * Nm D * L.sc.a) + Real.log p) +
      (K.dl1 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.log (2 * L.sc.a) +
        K.dl2 * ((topsBC D p).card : ℝ) * Real.log (2 * L.sc.a) ^ 2 / Real.log p) := by
    unfold rest EatI Real.logb
    rw [← dec_real _ (max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlp0.ne']
    congr 1
    ring
  have h1 := i_real (Real.log p) (gam p) ((topsBC D p).card : ℝ) (L.sc.b + L.etaSz + 1 + 3 * L.Sc) p
    (D.R.f : ℝ) L.sc.b hlp0.le hp0 (gam_le p hp.two_le) (gam_nonneg p hp.two_le) (card_topsBC_le p)
    (Nat.cast_nonneg _) (by linarith) (by linarith)
  have hw : ∀ z ∈ kindBC D p, 0 ≤ wPl D j z ∧ wPl D j z ≤ 5 * L.sc.b := fun z _ => by
    have := stepW D L hSz hbb j hj z
    exact ⟨this.1, by linarith [this.2]⟩
  have hs0 : 0 ≤ ∑ z ∈ kindBC D p, wPl D j z := Finset.sum_nonneg fun z hz => (hw z hz).1
  have hs : ∑ z ∈ kindBC D p, wPl D j z ≤ (D.R.f : ℝ) * (5 * L.sc.b) := by
    calc ∑ z ∈ kindBC D p, wPl D j z ≤ ∑ _z ∈ kindBC D p, 5 * L.sc.b :=
          Finset.sum_le_sum fun z hz => (hw z hz).2
      _ = ((kindBC D p).card : ℝ) * (5 * L.sc.b) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (D.R.f : ℝ) * (5 * L.sc.b) :=
          mul_le_mul_of_nonneg_right (card_kindBC_le p) (by linarith)
  have h2 := ii_real (Real.log p) ce.c6 (∑ z ∈ kindBC D p, wPl D j z) p (D.R.f : ℝ) L.sc.b hlp0.le hp0 hs0 hs
  have h8 : 1 ≤ 8 * (D.R.n : ℝ) * Nm D * L.sc.a := by
    have : 1 ≤ (D.R.n : ℝ) * Nm D * L.sc.a :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hNm1) ha1
    linarith
  have hl8 : 0 ≤ Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a) := Real.log_nonneg h8
  have hNa : 0 ≤ Nm D * L.sc.a := mul_nonneg (by linarith) (a_pos L).le
  have hnP0 : (0 : ℝ) ≤ (nP D p : ℝ) := Nat.cast_nonneg _
  have hY0 : 0 ≤ 4 * (nP D p : ℝ) * Nm D * L.sc.a := by
    have : 4 * (nP D p : ℝ) * Nm D * L.sc.a = 4 * (nP D p : ℝ) * (Nm D * L.sc.a) := by ring
    rw [this]; positivity
  have hYle : 4 * (nP D p : ℝ) * Nm D * L.sc.a ≤ 8 * (D.R.n : ℝ) * Nm D * L.sc.a := by
    have hn := nP_le_nW (D := D) p
    have e1 : 4 * (nP D p : ℝ) * Nm D * L.sc.a = (4 * (nP D p : ℝ)) * (Nm D * L.sc.a) := by ring
    have e2 : 8 * (D.R.n : ℝ) * Nm D * L.sc.a = (8 * (D.R.n : ℝ)) * (Nm D * L.sc.a) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) hNa
  have hY : Real.log (4 * (nP D p : ℝ) * Nm D * L.sc.a) ≤ Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a) := by
    rcases eq_or_lt_of_le hY0 with h | h
    · rw [← h, Real.log_zero]; exact hl8
    · exact Real.log_le_log h hYle
  have hpX' : Real.log p ≤ Real.log (L.sc.X'' D.R.n) := Real.log_le_log hp0 hpX
  have h3 := iii_real ((kindBC D p).card : ℝ) (D.R.N (j - 1) : ℝ) (D.R.N j : ℝ) (D.R.f : ℝ) (Nm D)
    (Real.log (4 * (nP D p : ℝ) * Nm D * L.sc.a)) (Real.log p) (Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a))
    (Real.log (L.sc.X'' D.R.n)) (card_kindBC_le p) (Nat.cast_nonneg _) (N_le_Nm (j - 1) (by omega))
    (N_le_Nm j hjm) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hY hpX' (by linarith)
  have h4 := iv_real K.dl1 K.dl2 ((kindBC D p).card : ℝ) ((topsBC D p).card : ℝ) (D.R.f : ℝ) (Nm D)
    (Real.log (2 * L.sc.a)) (Real.log p) (card_kindBC_le p) (card_topsBC_le p) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Real.log_nonneg (by linarith)) hlp2
  have hfin : c1 ce * (D.R.f : ℝ) * L.sc.b * (Real.log p / p) + (D.R.f : ℝ) * Rt L K =
      12 * (D.R.f : ℝ) * L.sc.b * (Real.log p / p) + 5 * |ce.c6| * (D.R.f : ℝ) * L.sc.b * (Real.log p / p) +
      (D.R.f : ℝ) * (Nm D ^ 2 * (Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a) +
        Real.log (L.sc.X'' D.R.n))) +
      (D.R.f : ℝ) * (|K.dl1| * Nm D ^ 2 * Real.log (2 * L.sc.a) + 2 * |K.dl2| * Real.log (2 * L.sc.a) ^ 2) := by
    unfold c1 Rt; ring
  rw [hdec, hfin]
  exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4

end PI.SzEatI.W
