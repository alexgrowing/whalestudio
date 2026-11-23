import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AutomorphicArithmetic.CharacterBoxes.Imports
import Development.AutomorphicArithmetic.CharacterBoxes.PairRows
import Development.AutomorphicArithmetic.CharacterBoxes.RealBox
import Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq
import Development.AutomorphicArithmetic.ThickFrames.topsChoiceH
import Development.AutomorphicArithmetic.ThickFrames.ThickFrame2Large
import Development.AutomorphicArithmetic.ShortNorms.MulLogLeRpowEventually
import Development.AutomorphicArithmetic.ShortNorms.levelData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

private theorem hof_quadraticChar_induces (d M : ℕ) [Fact d.Prime] (hd : d % 4 = 3) (hM : M ≠ 1) :
    GlobalTheoryTheory.Induces ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d)
      (GlobalTheoryTheory.chDir d) M := by
  have hp : d.Prime := Fact.out
  haveI : NeZero d := ⟨hp.ne_zero⟩
  have hch : ringChar (ZMod d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  refine ⟨?_, fun a ha => ?_⟩
  · rcases (Nat.dvd_prime hp).1 (DirichletCharacter.conductor_dvd_level
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)
        ((MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).2 (quadraticChar_ne_one hch))
    · exact h
  · have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; exact absurd (Nat.coprime_zero_left M |>.1 ha) hM
      · exact h
    rw [GlobalTheoryTheory.chDir, GlobalTheoryTheory.kron, GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 d a hd ha0,
      ← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
    simp

private theorem hof_abs_dlogH_le {R : Ranks} (H : Host R) {x eps C : ℝ} (h : QDq x eps C H.q H.d) :
    |dlogH H| ≤ C * Real.log x := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  have hd : H.d % 16 = 7 := H.hyp.2.2.2.1
  have h1 := (h.2.1 H.d _ (hof_quadraticChar_induces H.d (8 * H.q * H.d) (by omega) (by
    rw [mul_assoc]; omega))).2
  exact (Complex.abs_re_le_norm _).trans h1

private theorem hof_log_le_rpow (eps C : ℝ) (he : 0 < eps) (hC : 0 < C) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → C * Real.log x ≤ x ^ eps := by
  have h := (isLittleO_log_rpow_atTop he).bound (inv_pos.2 hC)
  obtain ⟨x0, h0⟩ := Filter.eventually_atTop.1 h
  refine ⟨max x0 1, fun x hx => ?_⟩
  have h1 := h0 x (le_of_max_le_left hx)
  have hx1 : 1 ≤ x := le_of_max_le_right hx
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg (by positivity)] at h1
  calc C * Real.log x ≤ C * (C⁻¹ * x ^ eps) := by gcongr
    _ = x ^ eps := by field_simp

private theorem hof_Lwv_le (s : Scale) (hy : 1 ≤ Real.log s.x) :
    (Lwv s : ℝ) ≤ (4084 + 60 / s.eps) * Real.log s.x := by
  have he := s.eps_pos
  have h1 : (⌈(405 : ℝ) * Real.log s.x⌉₊ : ℝ) < 405 * Real.log s.x + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have h2 : (⌈30 / s.eps⌉₊ : ℝ) < 30 / s.eps + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : 60 / s.eps = 2 * (30 / s.eps) := by ring
  have h4 : 0 < 30 / s.eps := by positivity
  unfold Lwv
  push_cast
  rw [h3]
  nlinarith [mul_nonneg h4.le (sub_nonneg.mpr hy)]

private theorem hof_thick :
    ∃ CT2 : ℝ, ∀ eps Co : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x →
      RankVal s R → (R.o : ℝ) ≤ Co → ∃ T : Finset ℕ, (∀ a ∈ T, 4 * Lwv s * a < R.n0) ∧ Formalism.FrobeniusOrbits.NoRel T (Lwv s) ∧
        (R.n0 : ℝ) * Real.exp (-(CT2 * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log (Lwv s)))) / (Lwv s) ≤ T.card ∧
        s.x ^ (-s.eps) * R.n ≤ (T.card : ℝ) ∧ 4 * Lwv s * T.card ≤ R.n0 ∧ 2 ≤ Lwv s := by
  obtain ⟨C, -, hT⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2
  refine ⟨C, fun eps Co he he' => ?_⟩
  obtain ⟨x0, hT⟩ := hT eps (max Co 2) (4084 + 60 / eps) he he'
  refine ⟨max x0 (Real.exp 1), fun s R hs hx hR ho => ?_⟩
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hy1 : 1 ≤ Real.log s.x := (Real.le_log_iff_exp_le hx0).mpr ((le_max_right _ _).trans hx)
  have hL : 2 ≤ Lwv s := by unfold Lwv; omega
  have hLK := hof_Lwv_le s hy1
  have hn1 := hR.n_lo
  have hn2 := hR.n_up
  rw [hs] at hLK hn1 hn2
  have hp0 : 0 < s.x ^ (2 + 8 * eps) := Real.rpow_pos_of_pos hx0 _
  have hlo : s.x ^ UpperTheory.BernoulliSumsFrobeniusOrbits.hE eps / 2 ≤ (R.n : ℝ) := by
    unfold UpperTheory.BernoulliSumsFrobeniusOrbits.hE
    linarith
  have hup : (R.n : ℝ) ≤ max Co 2 * s.x ^ UpperTheory.BernoulliSumsFrobeniusOrbits.hE eps :=
    hn2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp0.le)
  obtain ⟨T, t1, t2, t3, t4, t5⟩ := hT s.x ((le_max_left _ _).trans hx) R.toFrame (Lwv s) hL hLK
    (ho.trans (le_max_left _ _)) hlo hup
  exact ⟨T, t1, t2, t3, hs ▸ t4, t5, hL⟩

private theorem hof_exists_host (R : Ranks) (H0 : HostAx R.toFrame) (hA : admitted R H0) (b : ℕ) (hF : FieldRows H0.toHostRaw b)
    (hbig : 4 * R.t * R.r + 1 < H0.q ∧ 4 * R.t * R.r + 1 < H0.d)
    (g : Fin 2 → ℕ) (p p' q0 : ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (hp : p.Prime) (hp' : p'.Prime)
    (hpp : p ≠ p') (hm : p % 15 = 1 ∧ p' % 15 = 1) (hpg : ∀ i, p ≠ g i ∧ p' ≠ g i)
    (T : Finset ℕ) (Lw : ℕ) (hL : 2 ≤ Lw) (hT : ∀ a ∈ T, 4 * Lw * a < R.n0) (hT' : Formalism.FrobeniusOrbits.NoRel T Lw) (CT2 : ℝ)
    (hS : ∀ l ∈ ({g 0, g 1, p, p', q0} : Finset ℕ), Nat.Coprime l H0.QS) :
    ∃ H : Host R, H.toHostAx = H0 ∧ H.splitBound = b ∧ H.g = g ∧ H.pde = p ∧ H.pde' = p' ∧
      H.levelPrimes = {g 0, g 1, p, p', q0} ∧ H.ccK = ⊤ ∧ H.T2 = T ∧ H.Lw = Lw ∧ H.CT2 = CT2 := by
  obtain ⟨D, rfl, h2, h3⟩ := hA b
    { levelPrimes := {g 0, g 1, p, p', q0}, g := g, g_prime := hg, g_ne := hne
      g_level := by intro i; fin_cases i <;> simp
      pde := p, pde' := p', pde_prime := hp, pde'_prime := hp', pde_ne := hpp, pde_level := by simp
      pde_mod := hm, pde_ne_g := hpg, ccK := ⊤, ccK_ne_bot := top_ne_bot
      ccK_primitive := fun m hm h => by
        have h1 := congrArg Ideal.absNorm (top_le_iff.1 h)
        rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, NumberField.RingOfIntegers.rank, H0.toHostRaw.finrank_K] at h1
        nlinarith
      ccK_split := fun P hP h => absurd (top_le_iff.1 h) hP.ne_top, ccK_coprime := by simp, ccK_coprimeS := by simp
      level_coprimeS := hS
      TT := ∅, T2 := T, u0 := 0, Lw := Lw, two_le_Lw := hL, second_set_range := hT, second_set_no_relation := hT', CT2 := CT2 } hF hbig
  have e := eq_of_heq h3
  exact ⟨D, rfl, h2, congrArg Choices.g e, congrArg Choices.pde e, congrArg Choices.pde' e, congrArg Choices.levelPrimes e,
    congrArg Choices.ccK e, congrArg Choices.T2 e, congrArg Choices.Lw e, congrArg Choices.CT2 e⟩

private theorem hof_coprime {l Q q d : ℕ} (h : l % (Q * q * d) = 1) : Nat.Coprime l Q := by
  have h1 : Nat.Coprime l (Q * q * d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]
  exact h1.coprime_mul_right_right.coprime_mul_right_right

private theorem hof_odd {Q k M : ℕ} (hQ : Q ≠ 0) (h : Q ∣ Nat.lcm (2 ^ k) M) :
    (∀ l : ℕ, l.Prime → l ∣ Q → l ∣ 2 * M) ∧ ordCompl[2] Q ∣ M := by
  have h' := h.trans (Nat.lcm_dvd_mul _ _)
  refine ⟨fun l hl hd => ?_, ?_⟩
  · rcases hl.dvd_mul.1 (hd.trans h') with h1 | h1
    · exact (hl.dvd_of_dvd_pow h1).mul_right _
    · exact h1.mul_left _
  · exact ((Nat.coprime_ordCompl Nat.prime_two hQ).symm.pow_right k).dvd_of_dvd_mul_left ((Nat.ordCompl_dvd _ _).trans h')

private theorem hof_box {R : Ranks} (H : Host R) {M : ℕ} {eps Y X : ℝ} (hM : 0 < M) (hQ : H.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M)
    (hG : PairGood M eps Y X H.q H.d) : BoxH H Y eps ∧ UpperTheory.Top.RealBox H.toHostRaw := by
  obtain ⟨h1, h2⟩ := hof_odd H.QS_pos.ne' hQ
  obtain ⟨a, b⟩ := UpperTheory.Top.realBox M R.toFrame H.toHostRaw eps Y X hM h1 h2 hG
  refine ⟨fun N _ χ hχ hr => ?_, b⟩
  have hle : ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hM h2
  have hmono : ∀ j, height (ordCompl[2] H.QS) eps Y j ≤ height M eps Y j := fun j => by
    unfold height
    gcongr
  have key := a ⟨N, χ, hχ.1⟩ ((isCharH_iff H χ).1 hχ) hr
  refine ⟨fun hd => ?_, fun hq hd => ?_⟩
  · obtain ⟨k1, k2⟩ := key (Or.inr hd)
    rw [if_pos hd] at k1 k2
    have e : 8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps * GlobalTheoryTheory.X2 Y eps = height (ordCompl[2] H.QS) eps Y 1 := by
      simp [height, GlobalTheoryTheory.X1, GlobalTheoryTheory.X2]
    rw [e]
    exact ⟨hχ.1, hr, k2, fun z z1 z2 => k1 z z1 (z2.trans (hmono _))⟩
  · obtain ⟨k1, k2⟩ := key (Or.inl hq)
    rw [if_neg hd] at k1 k2
    have e : 8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps = height (ordCompl[2] H.QS) eps Y 0 := by
      simp [height, GlobalTheoryTheory.X1]
    rw [e]
    exact ⟨hχ.1, hr, k2, fun z z1 z2 => k1 z z1 (z2.trans (hmono _))⟩

theorem UpperTheory.T3.hostOfFieldOf :
    UpperTheory.T3.ShortNorm → UpperTheory.T3.SmallOne → ∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C0 → ∃ CT2 C8 c6 Cb x0 : ℝ, C0 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧
      ∀ (s : Scale) (R : Ranks) (H0 : HostAx R.toFrame) (M : ℕ) (Y : ℝ), s.eps = eps → x0 ≤ s.x → RankVal s R →
        s.J ≤ C0 → (R.o : ℝ) ≤ C0 → (H0.QS : ℝ) ≤ C0 * R.n → 0 < M → (M : ℝ) ≤ C0 → H0.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M →
        PairWin s Y → PairGood M eps Y s.x H0.q H0.d → FieldRows H0.toHostRaw ⌊Y ^ (eps / 5)⌋₊ → admitted R H0 →
        ∃ (H : Host R) (q0 : ℕ), H.toHostAx = H0 ∧ H.CT2 = CT2 ∧ HostGood s C8 4 c6 Cb H q0 ∧
          R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps)) := by
  intro hSN hSO eps C0 he he' hC0
  obtain ⟨C1, hC1, hL⟩ := UpperTheory.T3.levelData hSN hSO
  obtain ⟨xa, hL⟩ := hL eps he he'
  obtain ⟨c6, hc6, hThin⟩ := QH.thinH
  obtain ⟨xb, hThin⟩ := hThin C0 eps he he'
  obtain ⟨Cb, xc, hCb, hTops⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.topsChoiceH eps C0 he he'
  obtain ⟨xd, hP⟩ := UpperTheory.Top.pairRows eps C0 he he'
  obtain ⟨CT2, hT⟩ := hof_thick
  obtain ⟨xe, hT⟩ := hT eps C0 he he'
  obtain ⟨xf, hlog⟩ := hof_log_le_rpow eps 4 he (by norm_num)
  obtain ⟨xg, hbig⟩ := UpperTheory.T3.qdBig eps C0 he he'
  refine ⟨CT2, max C0 C1, c6, Cb, max (max (max xa xb) (max xc xd)) (max (max xe xf) xg), le_max_left _ _, hc6, hCb,
    fun s R H0 M Y hs hx hR hJ ho hQS hM hMC hQ hW hG hF hA => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, ⟨hxe, hf⟩, hg⟩ := hx
  subst hs
  obtain ⟨hqd, h100⟩ := hbig s R Y H0.q H0.d rfl hg hR hJ hW hG.pair
  have hN : Real.log ((H0.QS : ℝ) * H0.q * H0.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    obtain ⟨c⟩ := nonempty_choices H0.toHostRaw
    obtain ⟨D0, h0, -⟩ := hA _ c hF hqd
    clear c
    subst h0
    have h1 := (hP s R D0 M Y rfl hd hR ⟨hJ, ho, hQS⟩ hM hW hG).1.2.2.2.2.2.2.2.2.2.2
    have h2 := hW.z_log_sq_le
    linarith
  have hN0 : 0 < H0.QS * H0.q * H0.d := Nat.mul_pos (Nat.mul_pos H0.QS_pos hG.pair.q_prime.pos) hG.pair.d_prime.pos
  have hN1 : 1 < H0.QS * H0.q * H0.d := lt_of_lt_of_le (by omega) (Nat.le_of_dvd hN0 (dvd_mul_left H0.d _))
  have hd4 : H0.d % 4 = 3 := by have := hG.pair.d_mod; omega
  obtain ⟨g, p, p', q0, hgi, hg01, hdisj, hp, hp', hq0, hpp, hq0p, hq0p', mp, mp', mq0, lp, lp', lq0, hpg⟩ :=
    hL s R (H0.QS * H0.q * H0.d) H0.d rfl ha hR ⟨hG.pair.d_prime, hd4, h100, hN0, dvd_mul_left _ _, by
      have h1 : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by have := s.one_lt_alt; positivity
      push_cast
      linarith⟩
  have hm : ((H0.QS * H0.q * H0.d : ℕ) : ℝ) ^ C1 ≤ ((H0.QS : ℝ) * H0.q * H0.d) ^ max C0 C1 := by
    push_cast
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN0) (le_max_right _ _)
  replace lp := lp.trans hm
  replace lp' := lp'.trans hm
  replace lq0 := lq0.trans hm
  replace mp := mod_lcm_of_mod_mul hN0 mp
  replace mp' := mod_lcm_of_mod_mul hN0 mp'
  obtain ⟨T, t1, t2, t3, t4, t5, t6⟩ := hT s R rfl hxe hR ho
  have hgm : ∀ i, g i % (H0.QS * H0.q * H0.d) = 1 := fun i =>
    Eq.trans (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd _ _ _ hd4 (hgi i).2.2.2).1 (Nat.mod_eq_of_lt hN1)
  obtain ⟨D, e1, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hof_exists_host R H0 hA _ hF hqd g p p' q0 (fun i => (hgi i).1) hg01
    hp hp' hpp ⟨(mod_of_mod_lcm hN1 mp).1, (mod_of_mod_lcm hN1 mp').1⟩ hpg T (Lwv s) t6 t1 t2 CT2 (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl
      exacts [hof_coprime (hgm 0), hof_coprime (hgm 1), hof_coprime (mod_of_mod_lcm hN1 mp).2,
        hof_coprime (mod_of_mod_lcm hN1 mp').2, hof_coprime mq0])
  subst e1 e4 e5 e6 e9 e11
  obtain ⟨hrow, hq, hbox, -⟩ := hP s R D M Y rfl hd hR ⟨hJ, ho, hQS⟩ hM hW hG
  obtain ⟨TT, tt1, tt2, hbad, hsh⟩ := hTops s R D rfl hc hR ⟨hJ, ho, hQS⟩ ⟨Y, hW, hrow⟩
  have hnorm := fun i => (GlobalTheory.Mem.An.normOne_iff_host R D _ _).1 (hgi i).2.2.2
  have hsplit := GlobalTheory.HostSplit.split_of_one_mod R D
  obtain ⟨bH, bR⟩ := hof_box { D with TT := TT } hM hQ hG
  have hC : C0 ≤ max C0 C1 := le_max_left _ _
  refine ⟨{ D with TT := TT }, q0, rfl, rfl, ⟨
    ⟨⟨Y, hW, hrow⟩, ⟨tt1, tt2⟩, t4, ⟨lp, lp'⟩, fun i => ⟨(hgi i).2.1, (hgi i).2.2.1⟩, e10, e8, ?_,
      hJ.trans hC, ho.trans hC, hQS.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))⟩,
    ⟨fun i => ?_, hgm, ⟨?_, ?_⟩, fun l hl => ?_⟩, ?_, ?_, hq, ⟨Y, hW, hrow, hbox, bH⟩, ?_, ?_, hbad, hdisj,
    hnorm, ⟨mp, mp'⟩, ⟨hq0, mq0, lq0, hq0p, hq0p'⟩, e7⟩, hsh⟩
  · exact (Nat.floor_le_floor (hW.rpow_ez_le (by norm_num))).trans e3.ge
  · obtain ⟨π, h1, h2, -⟩ := hnorm i
    exact ⟨π, h1, h2⟩
  · exact (GlobalTheory.HostSplit.ncard_placesOver D.E hp).symm.trans (hsplit _ hp (mod_of_mod_lcm hN1 mp).2).1
  · exact (GlobalTheory.HostSplit.ncard_placesOver D.E hp').symm.trans (hsplit _ hp' (mod_of_mod_lcm hN1 mp').2).1
  · have hl' : l ∈ D.levelPrimes := hl
    rw [e7] at hl'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with rfl | rfl | rfl | rfl | rfl
    · exact (hsplit _ (hgi 0).1 (hgm 0)).2
    · exact (hsplit _ (hgi 1).1 (hgm 1)).2
    · exact (hsplit _ hp (mod_of_mod_lcm hN1 mp).2).2
    · exact (hsplit _ hp' (mod_of_mod_lcm hN1 mp').2).2
    · exact (hsplit _ hq0 mq0).2
  · rw [← e10] at t3
    exact t3
  · rw [← e10] at t5
    exact t5
  · exact (hof_abs_dlogH_le { D with TT := TT } hq).trans (hlog s.x hf)
  · refine (thinScales_iff_hostBound s c6 _).2 (hThin s.x hb R.toFrame D.toHostRaw ?_ ?_ bR)
    · have h1 : ((ordCompl[2] D.QS : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hM (hof_odd D.QS_pos.ne' hQ).2
      exact h1.trans hMC
    · have h1 : (D.condN : ℝ) = (D.QS : ℝ) * D.q * D.d := by
        rw [show D.condN = D.QS * D.q * D.d from rfl]
        push_cast
        rfl
      rw [h1]
      exact hN
