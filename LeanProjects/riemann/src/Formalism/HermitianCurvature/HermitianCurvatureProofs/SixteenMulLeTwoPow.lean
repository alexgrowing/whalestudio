import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryAOfPropositionA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VandermondeRatioHarmonic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaBoundOnBoundary
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmRingIdempotentUnitRatioIdentity

namespace Formalism.FourierDecayAlt.P.Sz9

open Finset Formalism.FourierDecayAlt.Sz

lemma sixteen_mul_le_two_pow (n : ℕ) (hn : 7 ≤ n) : n * 16 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h16 : 16 ≤ 2 ^ k :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    linarith

lemma small_f (f k : ℕ) (hfk : f ≤ k) (hk : 7 ≤ k) : (f : ℝ) * (8 / 2 ^ k) ≤ Real.log 2 := by
  have h1 := sixteen_mul_le_two_pow k hk
  have h2 : (k : ℝ) * 16 ≤ (2 : ℝ) ^ k := by exact_mod_cast h1
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hf : (f : ℝ) ≤ k := by exact_mod_cast hfk
  have hlog := Real.log_two_gt_d9
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith [mul_lt_mul_of_pos_right hlog hpos]

lemma vand_pos (p : ℕ) (x : ℕ → ℝ) (h : ∀ s t, 1 ≤ s → s < t → t ≤ p → x t < x s) :
    0 < Vand p x := by
  unfold Vand
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_Icc] at hi
  rw [Finset.mem_Ioc] at hj
  have hx := h i j hi.1 hj.1 hj.2
  linarith

lemma anti_of_step (p : ℕ) (x : ℕ → ℝ) (h : ∀ i, 1 ≤ i → i < p → x (i + 1) < x i) :
    ∀ s t, 1 ≤ s → s < t → t ≤ p → x t < x s := by
  intro s t hs hst htp
  obtain ⟨d, rfl⟩ : ∃ d, t = s + 1 + d := ⟨t - (s + 1), by omega⟩
  induction d with
  | zero => simpa using h s hs (by omega)
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := h (s + 1 + d) (by omega) (by omega)
    have e : s + 1 + (d + 1) = s + 1 + d + 1 := by omega
    rw [e]
    linarith

lemma vand_word_pos (hIL : Interlacing) (c : Cfg) (de : ℕ → ℝ) (hOk : c.Ok)
    (hde : IsWord c.k de) : 0 < Vand c.k (c.u de) := by
  unfold Interlacing at hIL
  obtain ⟨h1, -⟩ := hIL c de hOk hde
  refine vand_pos _ _ (anti_of_step _ _ (fun i hi1 hi2 => ?_))
  have hx := h1 i hi1 hi2
  linarith [hx.1, hx.2]

lemma sfac_pos (p : ℕ) : 0 < sfac p := by
  unfold sfac
  exact Finset.prod_pos (fun i _ => Nat.factorial_pos i)

lemma tcrit_nonneg (k m : ℕ) (ka rd g VV Vu : ℝ) (hka : 0 < ka) (hrd : 0 < rd) (hg : 0 < g)
    (hVV : 0 < VV) (hVu : 0 < Vu) : 0 ≤ Tcrit k m ka rd g VV Vu := by
  unfold Tcrit
  apply Real.rpow_nonneg
  unfold TcritPow
  positivity

lemma beta_bound (hBeta : BetaOnCut) (hAZ : AZeroBound) (c : Cfg) (r : ℕ) (bb : ℝ)
    (de de' : ℕ → ℝ) (ka rd g VV T T' : ℝ) (l : ℕ)
    (hOk : c.Ok) (hm : c.m = 2 * r + 2) (hSm : c.Small bb) (hde : IsWord c.k de)
    (hde' : IsWord c.k de') (hrd : 1 ≤ rd) (hka : ka = 2 * Real.pi / rd) (hg : 2 * Real.pi ≤ g)
    (hFD : FormalDegreeLower c (1 / 2) VV) (hT : 0 < T) (hT' : 0 < T') (hl1 : 1 ≤ l)
    (hl2 : l + 2 ≤ c.k) (hdl : de l ≠ de' l) (D : ℝ) (hD : D ≤ c.Del / 2) (Y : ℝ)
    (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ D) :
    0 ≤ g ^ c.m * c.be ka de de' T T' Y ∧
      g ^ c.m * c.be ka de de' T T' Y ≤
        160 * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt (D / c.Del) := by
  have hpi := Real.pi_pos
  have hg0 : 0 < g := by linarith
  have hka0 : 0 < ka := by rw [hka]; positivity
  have hDel : 0 < c.Del := by linarith [hOk.hDel]
  constructor
  · unfold Cfg.be Cfg.core
    positivity
  · have hYI : Y ∈ c.cutI l := ⟨hY1, hY2.trans hD⟩
    have h := hBeta c r bb de de' ka rd g VV T T' Y l hOk hm hSm hde hde' hrd hka hg hFD hT hT'
      hl1 hl2 hdl hYI
    have hA := (hAZ c bb hOk hSm).2
    have ht : 0 ≤ tv c de de' ka rd g VV T T' := by unfold tv; exact Real.sqrt_nonneg _
    have hs : Real.sqrt ((c.v l + Y) / c.Del) ≤ Real.sqrt (D / c.Del) := by
      apply Real.sqrt_le_sqrt
      gcongr
    calc g ^ c.m * c.be ka de de' T T' Y
        ≤ AZero c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k *
          Real.sqrt ((c.v l + Y) / c.Del) := h
      _ ≤ 160 * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt (D / c.Del) := by
          gcongr

end Formalism.FourierDecayAlt.P.Sz9

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz9

set_option maxHeartbeats 1000000 in

theorem sz_sizesMain_of (hCorA : CorA) (hBeta : BetaOnCut) (hAZ : AZeroBound)
    (hIL : Interlacing) (hLA : LamAnti) (hTP : ThresholdProducts) (hTL : ThetaLower) (hThP : ThetaPower)
    (hFS : FinalSmall) : SizesMain := by
  intro CA C0 CG CDel cT Cb hCA hC0 hCG hCDel hcT hCb hcTCb
  have hc : 0 < cExp CDel cT Cb := by
    unfold cExp
    have : 0 < min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := lt_min (by linarith) (by linarith)
    positivity
  obtain ⟨Ct, hCt⟩ : ∃ Ct : ℝ, Ct = 2 * C0 * Real.exp (1 / 4) := ⟨_, rfl⟩
  have hCt1 : 1 ≤ Ct := by
    have : 1 ≤ Real.exp (1 / 4) := Real.one_le_exp (by norm_num)
    rw [hCt]; nlinarith
  obtain ⟨k1, hk1⟩ := hThP CA 160 Ct CDel cT Cb hCA (by norm_num) hCt1 hCDel hcT hCb hcTCb
  obtain ⟨k2, hk2⟩ := hFS CA (cExp CDel cT Cb) hCA hc
  refine ⟨max 7 (max k1 k2), ?_⟩
  intro ι _ G bb C' Cf Th de de' T T' du du' l hk H hde hde' hl1 hl2 hdl hT hT' hC' hkbig hMR hLB
    hCC hCC' hCh hCh' hFD hTh hGr
  have hk7 : 7 ≤ G.k := le_trans (le_max_left _ _) hk
  have hkk1 : k1 ≤ G.k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkk2 : k2 ≤ G.k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hkR : (7 : ℝ) ≤ G.k := by exact_mod_cast hk7
  have hm2 : 2 ≤ G.m := by unfold Glob.m; omega
  have hf2 : 2 ≤ G.f := le_trans hm2 H.hmf
  have hbb := H.hbb
  have hv := H.hv
  have hpi := Real.pi_pos
  have hne : Nonempty ι := by
    have : 0 < Fintype.card ι := lt_of_lt_of_le (by norm_num) hf2
    exact Fintype.card_pos_iff.1 this
  obtain ⟨w0⟩ := hne

  have hbbk : (G.k : ℝ) ^ (Cb / 2) ≤ bb := by
    have h1 : (G.k : ℝ) ^ Cb ≤ G.b w0 1 := H.hnode w0 1 le_rfl (by omega)
    have h2 : G.b w0 1 ≤ bb ^ 2 := (H.hsmall w0).hbj 1 le_rfl (by show 1 ≤ 2 * G.r + 2; omega)
    have h3 : ((G.k : ℝ) ^ (Cb / 2)) ^ 2 = (G.k : ℝ) ^ Cb := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast; ring
    have h4 : ((G.k : ℝ) ^ (Cb / 2)) ^ 2 ≤ bb ^ 2 := by rw [h3]; exact h1.trans h2
    exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by norm_num)).1 h4
  have hpw : 1 < bb ^ (cT * (G.m : ℝ)) := by
    apply Real.one_lt_rpow hbb
    have : (0 : ℝ) < G.m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm2)
    positivity
  have hTR : (1 : ℝ) < T := lt_of_lt_of_le hpw hT
  have hTR' : (1 : ℝ) < T' := lt_of_lt_of_le hpw hT'
  have hT2 : 2 ≤ T := by
    have : 1 < T := by exact_mod_cast hTR
    omega
  have hT2' : 2 ≤ T' := by
    have : 1 < T' := by exact_mod_cast hTR'
    omega
  have hTT : (bb ^ (cT * (G.m : ℝ))) ^ 2 ≤ (T : ℝ) * T' := by
    rw [sq]
    exact mul_le_mul hT hT' (by linarith) (by linarith)
  have hTTpos : (0 : ℝ) < (T : ℝ) * T' := mul_pos (by linarith) (by linarith)
  have hNm : G.N = 10 * (G.m : ℝ) := by
    unfold Glob.N Glob.m; push_cast; ring
  have hN20 : 20 ≤ G.N := by
    unfold Glob.N
    have : (0 : ℝ) ≤ G.r := Nat.cast_nonneg _
    linarith
  have hN : 0 < G.N := by linarith
  obtain ⟨hCpi, hmin⟩ := hk1 G.k G.m G.f bb G.N G.lenI G.Del ((T : ℝ) * T') hkk1 hm2 H.hmf H.hfk
    hNm rfl hbbk H.hDel hTT
  have hkc1 : 1 ≤ (G.k : ℝ) ^ cExp CDel cT Cb := Real.one_le_rpow (by linarith) hc.le

  have hDelBig : 160 ^ 2 * ((G.k : ℝ) * G.N ^ 3) ≤ G.Del := by
    have h1 : (G.k : ℝ) ^ cExp CDel cT Cb ≤
        Real.sqrt (G.Del / (G.k * G.N ^ 3)) / (Ct * CA * 160) :=
      le_trans hmin (le_trans (min_le_left _ _) (min_le_left _ _))
    have hpos : 0 < Ct * CA * 160 := by positivity
    have h2 : Ct * CA * 160 ≤ Real.sqrt (G.Del / (G.k * G.N ^ 3)) := by
      have := (le_div_iff₀ hpos).1 (le_trans hkc1 h1)
      linarith
    have h3 : (160 : ℝ) ≤ Real.sqrt (G.Del / (G.k * G.N ^ 3)) := by
      have : 1 ≤ Ct * CA := one_le_mul_of_one_le_of_one_le hCt1 hCA
      linarith
    have h4 := (Real.le_sqrt' (by norm_num : (0 : ℝ) < 160)).1 h3
    have hkN : 0 < (G.k : ℝ) * G.N ^ 3 := by positivity
    exact (le_div_iff₀ hkN).1 h4
  have hN3 : 1 ≤ G.N ^ 3 := one_le_pow₀ (by linarith)
  have hkN3 : G.N ^ 3 ≤ (G.k : ℝ) * G.N ^ 3 := le_mul_of_one_le_left (by linarith) (by linarith)
  have hN3Del : G.N ^ 3 ≤ G.Del / 2 := by linarith
  have hDelpos : 0 < G.Del := by linarith
  have hI : 0 < G.lenI := by unfold Glob.lenI; linarith

  have hkb : (4 : ℝ) ≤ ((G.k : ℝ) * bb) ^ 8 := by
    have h1 : (4 : ℝ) ≤ (G.k : ℝ) * bb := by
      have := mul_le_mul hkR hbb.le zero_le_one (by linarith)
      linarith
    exact le_trans h1 (le_self_pow₀ (by linarith) (by norm_num))
  have hg1R : (4 : ℝ) ≤ G.g1 := le_trans hkb H.hg1
  have hg2R : (4 : ℝ) ≤ G.g2 := le_trans hkb H.hg2
  have hg1N : 4 ≤ G.g1 := by exact_mod_cast hg1R
  have hg2N : 4 ≤ G.g2 := by exact_mod_cast hg2R
  have hg16 : 16 ≤ G.g := by
    have := mul_le_mul hg1R hg2R (by norm_num) (by linarith)
    unfold Glob.g; linarith
  have h2pig : 2 * Real.pi ≤ G.g := by linarith [Real.pi_le_four]
  have hgpos : 0 < G.g := by linarith
  have hka : G.ka = 2 * Real.pi / (2 * G.v) := by
    unfold Glob.ka; field_simp
  have hkapos : 0 < G.ka := by unfold Glob.ka; positivity
  have hkapi : G.ka ≤ Real.pi := by
    unfold Glob.ka
    exact div_le_self hpi.le hv

  have hVu : ∀ w, 0 < Vand G.k ((G.place w).u de) := fun w =>
    vand_word_pos hIL (G.place w) de (H.hplace w) hde
  have hVu' : ∀ w, 0 < Vand G.k ((G.place w).u de') := fun w =>
    vand_word_pos hIL (G.place w) de' (H.hplace w) hde'
  have hVV : ∀ w, 0 < (G.size de T du).VV w := by
    intro w
    have h1 : 0 < Vand ((G.place w).k + (G.place w).m - 1) (G.place w).lam :=
      vand_pos _ _ (hLA (G.place w) (H.hplace w))
    have h2 := hFD w
    unfold FormalDegreeLower at h2
    linarith
  have hdsig : ∀ w, 0 < G.dsig w := by
    intro w
    have h1 : 0 < G.dsig w * (sfac (G.size de T du).n : ℝ) := hVV w
    have h2 : (0 : ℝ) < (sfac (G.size de T du).n : ℝ) := by exact_mod_cast sfac_pos _
    exact (mul_pos_iff_of_pos_right h2).1 h1

  have hsm := small_f G.f G.k H.hfk hk7
  have hlogbb : 0 ≤ Real.log bb := Real.log_nonneg hbb.le
  have hOkS : (G.size de T du).Ok :=
    ⟨(by omega : 1 ≤ G.k), (by linarith : 0 < G.v), H.hdF, (by omega : 2 ≤ G.g1),
      (by omega : 2 ≤ G.g2), hT2, H.hvol, hVu⟩
  have hOkS' : (G.size de' T' du').Ok :=
    ⟨(by omega : 1 ≤ G.k), (by linarith : 0 < G.v), H.hdF, (by omega : 2 ≤ G.g1),
      (by omega : 2 ≤ G.g2), hT2', H.hvol, hVu'⟩
  have hA := hCorA ι (G.size de T du) C0 CG C' (Real.log bb) hOkS hMR hLB hCC hdsig
    (by omega : 2 ≤ G.k) hg1N hg2N hC0 hCG hlogbb hC' hkbig hsm hCh
  have hA' := hCorA ι (G.size de' T' du') C0 CG C' (Real.log bb) hOkS' hMR hLB hCC' hdsig
    (by omega : 2 ≤ G.k) hg1N hg2N hC0 hCG hlogbb hC' hkbig hsm hCh'
  have hP : ∏ w, ((G.size de T du).Tcrit w / (T : ℝ)) ≤ Ct := by
    rw [hCt]; exact le_trans hA.2.1 hA.2.2
  have hP' : ∏ w, ((G.size de' T' du').Tcrit w / (T' : ℝ)) ≤ Ct := by
    rw [hCt]; exact le_trans hA'.2.1 hA'.2.2
  have hTc : ∀ w, 0 ≤ (G.size de T du).Tcrit w := fun w =>
    tcrit_nonneg _ _ _ _ _ _ _ hkapos (by show 0 < 2 * G.v; linarith) hgpos (hVV w) (hVu w)
  have hTc' : ∀ w, 0 ≤ (G.size de' T' du').Tcrit w := fun w =>
    tcrit_nonneg _ _ _ _ _ _ _ hkapos (by show 0 < 2 * G.v; linarith) hgpos (hVV w) (hVu' w)
  obtain ⟨t, ht⟩ : ∃ t : ι → ℝ, t = fun w =>
      tv (G.place w) de de' G.ka (2 * G.v) G.g ((G.size de T du).VV w) T T' := ⟨_, rfl⟩
  have ht0 : ∀ w, 0 ≤ t w := by
    intro w; rw [ht]; exact Real.sqrt_nonneg _
  have htsq : ∀ w, t w ^ 2 =
      ((G.size de T du).Tcrit w / (T : ℝ)) * ((G.size de' T' du').Tcrit w / (T' : ℝ)) := by
    intro w
    rw [ht]
    show (Real.sqrt ((G.size de T du).Tcrit w * (G.size de' T' du').Tcrit w /
      ((T : ℝ) * T'))) ^ 2 = _
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (hTc w) (hTc' w)) hTTpos.le), div_mul_div_comm]
  have htprod : ∏ w, t w ≤ Ct := by
    have h1 : (∏ w, t w) ^ 2 ≤ Ct ^ 2 := by
      rw [← prod_pow, prod_congr rfl (fun w _ => htsq w), prod_mul_distrib, sq]
      apply mul_le_mul hP hP' _ (by linarith)
      exact prod_nonneg fun w _ => div_nonneg (hTc' w) (by linarith)
    exact (pow_le_pow_iff_left₀ (prod_nonneg fun w _ => ht0 w) (by linarith) (by norm_num)).1 h1

  have hbd : ∀ (w : ι) (D : ℝ), D ≤ G.Del / 2 → ∀ Y : ℝ, 5 / 2 ≤ (G.place w).v l + Y →
      (G.place w).v l + Y ≤ D →
      0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y ∧
        G.g ^ G.m * (G.place w).be G.ka de de' T T' Y ≤
          160 * t w * Real.sqrt G.k * Real.sqrt (D / G.Del) := by
    intro w D hD Y hY1 hY2
    rw [ht]
    exact beta_bound hBeta hAZ (G.place w) G.r bb de de' G.ka (2 * G.v) G.g
      ((G.size de T du).VV w) T T' l (H.hplace w) rfl (H.hsmall w) hde hde' (by linarith) hka h2pig
      (hFD w) (by linarith) (by linarith) hl1 hl2 hdl D hD Y hY1 hY2
  have hB1 : ∀ w, 0 ≤ G.cutSupLong de de' T T' l w ∧ G.cutSupLong de de' T T' l w ≤
      160 * t w * Real.sqrt G.k * Real.sqrt (G.N ^ 3 / G.Del) := by
    intro w
    unfold Glob.cutSupLong
    constructor
    · apply Real.sSup_nonneg
      rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
      exact (hbd w _ hN3Del Y hY1 hY2).1
    · apply Real.sSup_le
      · rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
        exact (hbd w _ hN3Del Y hY1 hY2).2
      · have := ht0 w
        positivity
  have hB : ∀ w, 0 ≤ G.supI de de' T T' l w ∧ G.supI de de' T T' l w ≤
      160 * t w * Real.sqrt G.k := by
    intro w
    have hs1 : Real.sqrt (G.Del / 2 / G.Del) ≤ 1 := by
      apply Real.sqrt_le_one.2
      rw [div_le_one hDelpos]; linarith
    have h0 : 0 ≤ 160 * t w * Real.sqrt G.k := by
      have := ht0 w
      positivity
    unfold Glob.supI
    constructor
    · apply Real.sSup_nonneg
      rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
      exact (hbd w _ le_rfl Y hY1 hY2).1
    · apply Real.sSup_le
      · rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
        exact le_trans (hbd w _ le_rfl Y hY1 hY2).2 (mul_le_of_le_one_right h0 hs1)
      · exact h0

  have key := fun i s : ℕ => hTP ι t (G.cutSupLong de de' T T' l) (G.supI de de' T T' l) G.k CA 160 Ct
    G.ka G.N G.lenI G.g G.Del ((T : ℝ) * T') i s hCA (by norm_num) (by linarith) hkapos hkapi hN hI
    (by linarith) hDelpos hTTpos hCpi ht0 htprod hB1 hB
  have hTheta : (G.k : ℝ) ^ cExp CDel cT Cb ≤ Th := by
    refine le_trans hmin ?_
    apply hTL G.f G.k CA 160 Ct G.N G.lenI G.Del ((T : ℝ) * T') Th (by omega) (by omega) hCA
      (by norm_num) hCt1 hN hI hDelpos hTTpos hTh hCpi
    obtain ⟨i, hi1, hi2, hcase⟩ := hGr.1
    rcases hcase with ⟨_, hx⟩ | ⟨h2i, hx⟩ | ⟨s, hs2, _, hx⟩ | hx
    · left; rw [hx]; exact (key 1 1 le_rfl).1
    · right; left; rw [hx]; exact (key i 1 hi1).2.1 h2i
    · right; right; left; rw [hx]; exact (key i s hi1).2.2.1 hs2
    · right; right; right; rw [hx]; exact (key i 1 hi1).2.2.2
  refine ⟨hTheta, ?_⟩
  intro h16 hCf
  exact hk2 G.k G.r G.f bb Cf Th hkk2 H.hmf hbb.le h16 hCf hTheta

theorem size_bounds_conclusion : Formalism.FourierDecayAlt.Sz.SizesMain :=
  sz_sizesMain_of corollary_a_of_proposition_a beta_bound_on_boundary a_zero_le_one_sixty interlacing
    lamStrictAnti threshold_products theta_lower_bound theta_power_bound final_smallness

end Formalism.FourierDecayAlt.P
