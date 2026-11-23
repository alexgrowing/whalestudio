import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise

namespace Formalism.FourierDecayAlt.P.Jx5

theorem sup_core {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (w : ι)
    (hg : 0 < G.g) (hk : 0 < G.ka) (S : Set ℝ) :
    sSup ((fun Y => G.g ^ G.m * (G.place w).be G.ka de de' T T' Y) '' S) /
        (G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹) =
      sSup ((fun Y => (G.place w).core de de' T T' Y) '' S) := by
  have ha : 0 < G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹ := by positivity
  have e : (fun Y => G.g ^ G.m * (G.place w).be G.ka de de' T T' Y) '' S =
      (G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹) • ((fun Y => (G.place w).core de de' T T' Y) '' S) := by
    rw [← Set.image_smul, Set.image_image]
    refine Set.image_congr fun Y _ => ?_
    show G.g ^ G.m * ((G.ka ^ (G.m - 1))⁻¹ * (G.place w).core de de' T T' Y) = _
    rw [smul_eq_mul, mul_assoc]
  rw [e, Real.sSup_smul_of_nonneg ha.le, smul_eq_mul, mul_div_cancel_left₀ _ ha.ne']

theorem lambda_threshold_mono (m i s : ℕ) {C C' κ N I A : ℝ} (hC : 0 ≤ C) (h : C ≤ C') (hκ : 0 ≤ κ) (hN : 0 ≤ N)
    (hI : 0 ≤ I) (hA : 0 ≤ A) :
    0 ≤ Sz.lamThreshold m i s C κ N I A ∧ Sz.lamThreshold m i s C κ N I A ≤ Sz.lamThreshold m i s C' κ N I A := by
  have hC' : 0 ≤ C' := hC.trans h
  unfold Sz.lamThreshold
  constructor
  · positivity
  · gcongr

theorem lamPrimeSq_mono (m i : ℕ) {C C' κ N I A TT : ℝ} (hC : 0 ≤ C) (h : C ≤ C') (hκ : 0 ≤ κ)
    (hN : 0 ≤ N) (hI : 0 ≤ I) (hA : 0 ≤ A) :
    Sz.lamPrimeSq m i C κ N I A TT ≤ Sz.lamPrimeSq m i C' κ N I A TT := by
  have hC' : 0 ≤ C' := hC.trans h
  unfold Sz.lamPrimeSq
  gcongr

theorem supA_nonneg {ι : Type} [Fintype ι] (G : Sz.Glob ι) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
    (one : Bool) (w : ι) (hg : 0 < G.g) (hv : 0 < G.v) : 0 ≤ supA G de de' T T' l one w := by
  have hka : 0 < G.ka := by unfold Sz.Glob.ka; positivity
  have hel : ∀ Y, 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y := by
    intro Y
    unfold Sz.Cfg.be Sz.Cfg.core
    positivity
  unfold supA
  apply div_nonneg _ (by positivity)
  cases one
  · simp only [Bool.false_eq_true, if_false]
    unfold Sz.Glob.supI
    apply Real.sSup_nonneg
    rintro x ⟨Y, _, rfl⟩
    exact hel Y
  · simp only [if_true]
    unfold Sz.Glob.cutSupLong
    apply Real.sSup_nonneg
    rintro x ⟨Y, _, rfl⟩
    exact hel Y

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma rd_pos' : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  have : discr E ≠ 0 := discr_ne_zero E
  exact_mod_cast abs_pos.mpr this

variable (G : Sz.Glob (InfinitePlace E)) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)

noncomputable def supBS (b s : ℕ) (w : InfinitePlace E) : ℝ :=
  if b = 1 ∧ s = 1 then G.cutSupLong de de' T T' l w else G.supI de de' T T' l w

lemma ka_eq (hv : G.v = S6.rd E / 2) : G.ka = 2 * Real.pi / S6.rd E := by
  have hrd := rd_pos' (E := E)
  unfold Sz.Glob.ka; rw [hv]; field_simp

lemma thrS_norm (hF : FrameProducts) (hv : G.v = S6.rd E / 2) (hg : 0 < G.g) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 1 ≤ s) (w : InfinitePlace E) :
    thrS G C de de' T T' l b s w * (G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) =
      Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) := by
  have hrd := rd_pos' (E := E)
  have hka := ka_eq G hv
  have hkap : 0 < G.ka := by rw [hka]; positivity
  have h := (hF G.r b s C (S6.rd E) G.g G.N G.lenI
    (supA G de de' T T' l (decide (b = 1 ∧ s = 1)) w) (T * T') hb hs hrd hg).1
  have hm : G.m = 2 * G.r + 2 := rfl
  unfold thrS
  rw [hm, h, ← hka]
  congr 1
  unfold supA supBS
  rw [hm]
  simp only [decide_eq_true_eq]
  field_simp

lemma thrP_norm (hF : FrameProducts) (hv : G.v = S6.rd E / 2) (hg : 0 < G.g) (b : ℕ) (hb : 1 ≤ b)
    (w : InfinitePlace E) :
    thrP G C de de' T T' l b w * (G.g * S6.rd E ^ (S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
      Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') := by
  have hrd := rd_pos' (E := E)
  have hka := ka_eq G hv
  have hkap : 0 < G.ka := by rw [hka]; positivity
  have h := (hF G.r b 1 C (S6.rd E) G.g G.N G.lenI
    (supA G de de' T T' l false w) (T * T') hb le_rfl hrd hg).2
  have hm : G.m = 2 * G.r + 2 := rfl
  unfold thrP
  rw [hm, h, ← hka]
  congr 1
  unfold supA
  rw [hm]
  simp only [Bool.false_eq_true, if_false]
  field_simp

end

end Formalism.FourierDecayAlt.P.Jx5

namespace Formalism.FourierDecayAlt.P

open Jx5

theorem supremum_A_is_majorant : SupAIsCore := by
  intro ι _ G de de' T T' l w hg hk
  constructor
  · exact sup_core G de de' T T' w hg hk _
  · exact sup_core G de de' T T' w hg hk _

theorem threshold_mono : ThresholdsMonotone := by
  intro ι _ G C C' de de' T T' l hC h hg hv hI b s w
  have hκ : 0 ≤ 2 * Real.pi / G.g := by positivity
  have hN : 0 ≤ G.N := by unfold Sz.Glob.N; positivity
  have h1 := lambda_threshold_mono G.m b s hC h hκ hN hI.le
    (supA_nonneg G de de' T T' l (decide (b = 1 ∧ s = 1)) w hg hv)
  refine ⟨h1.1, h1.2, Real.sqrt_nonneg _, Real.sqrt_le_sqrt ?_⟩
  exact lamPrimeSq_mono G.m b hC h hκ hN hI.le (supA_nonneg G de de' T T' l false w hg hv)

theorem instance_sizes : InstSizes := by
  intro hLG hIM hNI hDF hFP hX E W _ _ _ D e G C de de' T T' l Θ hU hInst hg1 hg2 hC hI hΘ hGr
  obtain ⟨hr, hK, hPl, hv, hLa, hLap, hLad, hszD, hszL, hvol⟩ := hInst
  have hrd := rd_pos' (E := E)
  have hg : 0 < G.g := by
    unfold Sz.Glob.g
    have a1 : (0:ℝ) < G.g1 := by exact_mod_cast hg1
    have a2 : (0:ℝ) < G.g2 := by exact_mod_cast hg2
    positivity
  have hgN : 0 < G.g1 * G.g2 := Nat.mul_pos hg1 hg2
  have hgc : ((G.g1 * G.g2 : ℕ) : ℝ) = G.g := by unfold Sz.Glob.g; push_cast; ring
  obtain ⟨_, hcard, hdeg⟩ := hDF E
  have hfd : G.f = S6.deg E := hcard
  have hfD : D.f = G.f := by
    have := Fintype.card_congr e
    simpa [Sz.Glob.f] using this
  have hka0 : 0 < G.ka := by rw [ka_eq G hv]; positivity
  have hN0 : 0 ≤ G.N := by unfold Sz.Glob.N; positivity
  have hND : ∀ ν : ℤ, √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) ν) : ℝ) =
      ((G.g * S6.rd E ^ (ν + 1)) ^ G.f)⁻¹ := by
    intro ν
    have := hNI E (G.g1 * G.g2) (-1) (-(ν + 1)) hgN
    unfold S6.dualIdl
    rw [this, hgc, hfd, ← inv_pow, mul_inv, zpow_neg, zpow_neg, zpow_one]
  have hNL : ∀ ν : ℤ, √(FractionalIdeal.absNorm (S6.liftIdl E (G.g1 * G.g2) ν) : ℝ) =
      ((G.g * S6.rd E ^ ν) ^ G.f)⁻¹ := by
    intro ν
    have := hNI E (G.g1 * G.g2) (-1) (-ν) hgN
    unfold S6.liftIdl
    rw [this, hgc, hfd, ← inv_pow, mul_inv, zpow_neg, zpow_neg, zpow_one]
  have hcp : ∀ ν : ℤ, 0 < G.g * S6.rd E ^ ν := fun ν => mul_pos hg (zpow_pos hrd _)
  have hbe : ∀ (w : InfinitePlace E) (Y : ℝ), 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y := by
    intro w Y
    exact mul_nonneg (pow_nonneg hg.le _)
      (mul_nonneg (inv_nonneg.2 (pow_nonneg hka0.le _)) (Real.sqrt_nonneg _))
  have hsI : ∀ w, 0 ≤ G.supI de de' T T' l w := by
    intro w; apply Real.sSup_nonneg; rintro x ⟨Y, _, rfl⟩; exact hbe w Y
  have hsI1 : ∀ w, 0 ≤ G.cutSupLong de de' T T' l w := by
    intro w; apply Real.sSup_nonneg; rintro x ⟨Y, _, rfl⟩; exact hbe w Y
  have hS0 : ∀ b s w, 0 ≤ supBS G de de' T T' l b s w := by
    intro b s w; unfold supBS; split_ifs
    · exact hsI1 w
    · exact hsI w
  have hlam0 : ∀ b s B, 0 ≤ B → 0 ≤ Sz.lamHat b s C G.ka G.N G.lenI G.g B := by
    intro b s B hB
    unfold Sz.lamHat
    exact mul_nonneg (mul_nonneg hC hB) (pow_nonneg (div_nonneg (mul_nonneg (mul_nonneg hC hka0.le) hN0)
      (mul_nonneg hg.le hI.le)) _)

  have hPle : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ G.r + 2 →
      ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) ≤ (Θ ^ G.f)⁻¹ := by
    intro b s hb hs hbs
    apply hGr.2
    refine ⟨b, hb, by omega, ?_⟩
    by_cases h1 : s = 1
    · subst h1
      by_cases hb1 : b = 1
      · subst hb1
        left
        refine ⟨rfl, Finset.prod_congr rfl fun w _ => ?_⟩
        rw [(hX 0 1 C G.ka G.N G.lenI 0 G.g _).2]; simp [supBS]
      · right; left
        refine ⟨by omega, Finset.prod_congr rfl fun w _ => ?_⟩
        rw [(hX 0 b C G.ka G.N G.lenI 0 G.g _).2]; simp [supBS, hb1]
    · right; right; left
      refine ⟨s, by omega, by omega, Finset.prod_congr rfl fun w _ => ?_⟩
      simp [supBS, h1]
  have hQle : ∀ b, 1 ≤ b → b ≤ G.r + 1 →
      ∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') ≤ (Θ ^ G.f)⁻¹ := by
    intro b hb hb'
    apply hGr.2
    exact ⟨b, hb, hb', Or.inr (Or.inr (Or.inr rfl))⟩
  have hthrw : ∀ b s, 1 ≤ b → 1 ≤ s → ∀ w, thrS G C de de' T T' l b s w =
      Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) /
        (G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) := by
    intro b s hb hs w
    rw [eq_div_iff (hcp _).ne']
    exact thrS_norm G C de de' T T' l hFP hv hg b s hb hs w
  have hthr : ∀ b s, 1 ≤ b → 1 ≤ s → ∏ w, thrS G C de de' T T' l b s w =
      (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w)) *
        ((G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) ^ G.f)⁻¹ := by
    intro b s hb hs
    rw [Finset.prod_congr rfl fun w _ => hthrw b s hb hs w, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, div_eq_mul_inv]
    rfl
  have hthr0 : ∀ b s, 1 ≤ b → 1 ≤ s → ∀ w, 0 ≤ thrS G C de de' T T' l b s w := by
    intro b s hb hs w
    rw [hthrw b s hb hs w]
    exact div_nonneg (hlam0 _ _ _ (hS0 _ _ _)) (hcp _).le
  have hP0 : ∀ b s, 0 ≤ ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (supBS G de de' T T' l b s w) :=
    fun b s => Finset.prod_nonneg fun w _ => hlam0 _ _ _ (hS0 _ _ _)
  have hΘf : 0 < (Θ ^ G.f)⁻¹ := by positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro b s
    rw [hvol]
    exact div_nonneg (sq_nonneg _) (Rat.cast_nonneg.2 (FractionalIdeal.absNorm_nonneg _))
  · intro b s hb hs hbs
    rw [hr] at hbs
    rw [hvol, hthr b s hb hs, ← hND, hfD]
    have hn : 0 < √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ) := by
      rw [hND]; exact inv_pos.2 (pow_pos (hcp _) _)
    have hn' := Real.sqrt_pos.1 hn
    rw [mul_pow, Real.sq_sqrt hn'.le, mul_div_assoc, div_self hn'.ne', mul_one]
    exact pow_le_pow_left₀ (hP0 b s) (hPle b s hb hs hbs) 2
  · intro i hi hi'
    rw [hr] at hi'
    have hn : 0 < √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r i 1)) : ℝ) := by
      rw [hND]; exact inv_pos.2 (pow_pos (hcp _) _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      simp only at h0
      rw [h0] at hn
      simp at hn
    · intro x hx
      rw [hLad] at hx
      exact (hLG E hU (G.g1 * G.g2) (S6.nuBlock G.r i 1) 1 hgN).2.2.2.2.1 hx
    · intro v; rw [hszD]; exact hthr0 i 1 hi le_rfl _
    · rw [Finset.prod_congr rfl fun v _ => hszD i v,
        Equiv.prod_comp e (fun w => thrS G C de de' T T' l i 1 w)]
      have := hthr i 1 hi le_rfl
      push_cast at this
      rw [this, ← hND, hfD, one_div, inv_pow]
      exact mul_le_mul_of_nonneg_right (hPle i 1 hi le_rfl (by omega)) hn.le
  · intro b s hb hs hbs hne
    rw [hr] at hbs hne
    have hn : 0 < √(FractionalIdeal.absNorm (S6.liftIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ) := by
      rw [hNL]; exact inv_pos.2 (pow_pos (hcp _) _)
    have h2 : (Θ ^ G.f)⁻¹ ≤ (2 / Θ) ^ G.f := by
      rw [div_pow, div_eq_mul_inv]
      have : (1:ℝ) ≤ 2 ^ G.f := one_le_pow₀ (by norm_num)
      nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      simp only at h0
      rw [h0] at hn
      simp at hn
    · intro x hx
      rw [hLap] at hx
      exact (hLG E hU (G.g1 * G.g2) (S6.nuBlock G.r b s) s hgN).2.2.2.2.2.2.1 hx
    · intro v; rw [hszL]; split_ifs
      · exact hthr0 b (s + 1) hb (by omega) _
      · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · beta_reduce
      by_cases hc : b + s ≤ G.r + 1
      · rw [Finset.prod_congr rfl fun v _ => (by rw [hszL, if_pos hc] :
          D.szL b s v = thrS G C de de' T T' l b (s + 1) (e v)),
          Equiv.prod_comp e (fun w => thrS G C de de' T T' l b (s + 1) w), hthr b (s + 1) hb (by omega), hfD]
        have hν : S6.nuBlock G.r b ((s + 1 : ℕ) : ℤ) + 1 = S6.nuBlock G.r b s := by
          unfold S6.nuBlock; push_cast; ring
        rw [hν, ← hNL]
        exact mul_le_mul_of_nonneg_right (le_trans (hPle b (s + 1) hb (by omega) (by omega)) h2) hn.le
      · rw [Finset.prod_congr rfl fun v _ => (by rw [hszL, if_neg hc] :
          D.szL b s v = 2 * thrP G C de de' T T' l b (e v)),
          Equiv.prod_comp e (fun w => 2 * thrP G C de de' T T' l b w), hfD]
        have hν : ((G.r : ℤ) + 2 - b) = s := by
          have : b + s = G.r + 2 := by omega
          have : ((b + s : ℕ) : ℤ) = ((G.r + 2 : ℕ) : ℤ) := by rw [this]
          push_cast at this; linarith
        have hw : ∀ w, 2 * thrP G C de de' T T' l b w =
            2 * Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') /
              (G.g * S6.rd E ^ (S6.nuBlock G.r b s)) := by
          intro w
          rw [eq_div_iff (hcp _).ne', mul_assoc, ← hν]
          rw [thrP_norm G C de de' T T' l hFP hv hg b hb w]
        rw [Finset.prod_congr rfl fun w _ => hw w, Finset.prod_div_distrib, Finset.prod_const,
          Finset.card_univ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, div_eq_mul_inv]
        change 2 ^ G.f * _ * ((G.g * S6.rd E ^ (S6.nuBlock G.r b s)) ^ G.f)⁻¹ ≤ _
        rw [← hNL, div_pow, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ hn.le
        exact mul_le_mul_of_nonneg_left (hQle b hb (by omega)) (by positivity)
  · unfold TB.Data.Ntop Sz.Glob.N
    rw [hK, hr]; push_cast; ring

theorem instance_lattice_sums : InstLatticeSums := by
  intro hL hI hB h1 h2 h3 h4 h5 h6
  obtain ⟨C, hC, H⟩ := hL hB
  refine ⟨C * 2 ^ ((5:ℝ) - 5 / 2), ?_, ?_⟩
  · have : (1:ℝ) ≤ 2 ^ ((5:ℝ) - 5 / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    nlinarith
  intro E W _ _ _ D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc hI' hΘ hG
  obtain ⟨hs, hid, _⟩ := hI h1 h2 h3 h4 h5 h6 E W D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc hI' (by linarith) hG
  refine ⟨hs, ?_⟩
  have hK : D.K = 5 := hInst.2.1
  have := H E W D e _ _ Θ 2 hInst.2.2.1 (by omega) (by norm_num) (by linarith) hid
  rw [hK] at this ⊢
  simpa using this

theorem sizes_to_recursion : SizesToRecursion := by
  intro hS CA C0 CG CDel cT Cb C C' hCA hC0 hCG hCDel hcT hCb hcTb hC hCCA
  obtain ⟨k0, H⟩ := hS CA C0 CG CDel cT Cb hCA hC0 hCG hCDel hcT hCb hcTb
  have hc : 0 < Sz.cExp CDel cT Cb := by
    unfold Sz.cExp
    have : 0 < min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := lt_min (by linarith) (by linarith)
    positivity
  obtain ⟨k1, hk1⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (max C' 5))
  refine ⟨max k0 k1, ?_⟩
  intro ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := hyp
  obtain ⟨hTh, hrest⟩ := H ι G bb Cp Cf Th de de' T T' du du' l (le_trans (le_max_left _ _) hk)
    a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  obtain ⟨ha, hb⟩ := hrest h16 hCf
  have hbig : max C' 5 ≤ Th := le_trans (hk1 G.k (le_trans (le_max_right _ _) hk)) hTh
  have hpow : (C / Th) ^ G.f ≤ (CA / Th) ^ G.f :=
    pow_le_pow_left₀ (div_nonneg hC a18.le) (div_le_div_of_nonneg_right hCCA a18.le) _
  have hp0 : 0 ≤ (C / Th) ^ G.f := pow_nonneg (div_nonneg hC a18.le) _
  have hr : (0:ℝ) ≤ G.r := Nat.cast_nonneg _
  have hb1 : (bb ^ 7)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ a1.hbb.le)
  have hx : ((G.r : ℝ) + 1) * (C / Th) ^ G.f ≤ ((G.r : ℝ) + 1) * (CA / Th) ^ G.f :=
    mul_le_mul_of_nonneg_left hpow (by linarith)
  have hx0 : 0 ≤ ((G.r : ℝ) + 1) * (C / Th) ^ G.f := mul_nonneg (by linarith) hp0
  have hb' : CA * (((G.r : ℝ) + 1) * (CA / Th) ^ G.f) ≤ (bb ^ 7)⁻¹ := by rw [← mul_assoc]; exact hb
  refine ⟨le_trans (le_max_left _ _) hbig, lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hbig), ?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_left hpow hr) ha
  · nlinarith
  · rw [mul_assoc]
    calc C * (((G.r : ℝ) + 1) * (C / Th) ^ G.f) ≤ CA * (((G.r : ℝ) + 1) * (CA / Th) ^ G.f) :=
          mul_le_mul hCCA hx hx0 (by linarith)
      _ ≤ _ := hb'

theorem global_positive : GlobPositive := by
  intro CDel Cb hCDel hCb
  refine ⟨max 3 ⌈2 / Cb⌉₊, ?_⟩
  intro ι _ G bb hk hyp
  have hk3 : 3 ≤ G.k := le_trans (le_max_left _ _) hk
  have hkC : 2 / Cb ≤ (G.k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)
  have hk3r : (3 : ℝ) ≤ G.k := by exact_mod_cast hk3
  have hk0 : (0 : ℝ) < G.k := by linarith
  have hbb := hyp.hbb
  have hbb0 : 0 < bb := by linarith
  have hpos : 0 < ((G.k : ℝ) * bb) ^ 8 := by positivity
  have hg1 : 0 < G.g1 := by
    have : (0 : ℝ) < G.g1 := lt_of_lt_of_le hpos hyp.hg1
    exact_mod_cast this
  have hg2 : 0 < G.g2 := by
    have : (0 : ℝ) < G.g2 := lt_of_lt_of_le hpos hyp.hg2
    exact_mod_cast this
  refine ⟨hg1, hg2, ?_⟩
  have hm2 : 2 ≤ G.m := by unfold Sz.Glob.m; omega
  have hf2 : 2 ≤ G.f := le_trans hm2 hyp.hmf
  have hne : Nonempty ι := by
    apply Fintype.card_pos_iff.1
    have : G.f = Fintype.card ι := rfl
    omega
  obtain ⟨w⟩ := hne
  have h1 : (G.k : ℝ) ^ Cb ≤ G.b w 1 := hyp.hnode w 1 le_rfl (by omega)
  have h2 : G.b w 1 ≤ bb ^ 2 := (hyp.hsmall w).hbj 1 le_rfl (by
    show 1 ≤ 2 * G.r + 2
    omega)
  have h3 : (G.k : ℝ) ^ Cb ≤ bb ^ 2 := le_trans h1 h2
  have h4 : Cb * Real.log G.k ≤ 2 * Real.log bb := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hk0 Cb) h3
    rw [Real.log_rpow hk0, Real.log_pow] at this
    exact_mod_cast this
  have hlogk : 1 ≤ Real.log G.k := by
    rw [Real.le_log_iff_exp_le hk0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogbb : Cb / 2 ≤ Real.log bb := by nlinarith
  have hkCb : 2 ≤ (G.k : ℝ) * Cb := by
    rw [div_le_iff₀ hCb] at hkC
    exact hkC
  have hf2r : (2 : ℝ) ≤ G.f := by exact_mod_cast hf2
  have hbase : 2 ≤ (G.k : ℝ) * G.f * Real.log bb := by
    have e1 : (G.k : ℝ) * 2 * (Cb / 2) ≤ (G.k : ℝ) * G.f * Real.log bb := by
      apply mul_le_mul _ hlogbb (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hf2r hk0.le
    nlinarith
  have h16 : (16 : ℝ) ≤ ((G.k : ℝ) * G.f * Real.log bb) ^ CDel := by
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ CDel := Real.rpow_le_rpow_of_exponent_le (by norm_num) hCDel.le
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hbase (by linarith)
  have hD : 16 ≤ G.Del := le_trans h16 hyp.hDel
  unfold Sz.Glob.lenI
  linarith

theorem majorant_mono : MajMono := by
  intro E W _ D ρ ρ' l h hav
  unfold TB.Data.maj
  apply Finset.prod_le_prod
  · intro v _
    exact le_min zero_le_one (pow_nonneg (div_nonneg (h v).1 (hav v)) _)
  · intro v _
    apply min_le_min le_rfl
    exact pow_le_pow_left₀ (div_nonneg (h v).1 (hav v)) (div_le_div_of_nonneg_right (h v).2 (hav v)) _

end Formalism.FourierDecayAlt.P
