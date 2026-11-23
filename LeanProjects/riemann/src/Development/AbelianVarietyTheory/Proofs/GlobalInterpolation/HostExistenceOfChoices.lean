import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsThinPrimeSetStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTwoLargeNormOnePrimesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimesInProgressionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElementsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
import Development.AutomorphicArithmetic.EvenBoxes.BoxBoundForHost

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.HostExist

theorem kronSym_of_odd (a : ℤ) {n : ℕ} (h : ¬ 2 ∣ n) : GlobalTheoryTheory.kronSym a n = jacobiSym a n := by
  simp [GlobalTheoryTheory.kronSym, Nat.factorization_eq_zero_of_not_dvd h]

theorem quadraticChar_induces (d M : ℕ) [Fact d.Prime] (hd : d % 4 = 3) (hM : M ≠ 1) :
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

theorem abs_dlogH_le {R : Ranks} (H : Host R) {x eps C : ℝ} (h : QDq x eps C H.q H.d) :
    |dlogH H| ≤ C * Real.log x := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  have hd : H.d % 16 = 7 := H.hyp.2.2.2.1
  have h1 := (h.2.1 H.d _ (quadraticChar_induces H.d (8 * H.q * H.d) (by omega) (by
    rw [mul_assoc]; omega))).2
  exact (Complex.abs_re_le_norm _).trans h1

theorem exists_host (R : Ranks) (q d B : ℕ) (hyp : Formalism.FrobeniusOrbits.HostHyp q d)
    (hbig : 4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d) (h3 : q ≠ 3) (he : 2 ≤ R.e)
    (hinj : Function.Injective R.h) (ho : R.o ^ 64 ≤ 2 ^ R.e)
    (hsp : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ B → jacobiSym (-(d : ℤ)) p = 1)
    (g : Fin 2 → ℕ) (p p' q0 : ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (hp : p.Prime) (hp' : p'.Prime)
    (hpp : p ≠ p') (hm : p % 15 = 1 ∧ p' % 15 = 1) (hpg : ∀ i, p ≠ g i ∧ p' ≠ g i)
    (hodd : ∀ l ∈ ({g 0, g 1, p, p', q0} : Finset ℕ), l % 2 = 1)
    (T : Finset ℕ) (Lw : ℕ) (hL : 2 ≤ Lw) (hT : ∀ a ∈ T, 4 * Lw * a < R.n0) (hT' : Formalism.FrobeniusOrbits.NoRel T Lw) (CT2 : ℝ) :
    ∃ H : Host R, H.q = q ∧ H.d = d ∧ H.splitBound = B ∧ H.g = g ∧ H.pde = p ∧ H.pde' = p' ∧
      H.levelPrimes = {g 0, g 1, p, p', q0} ∧ H.ccK = ⊤ ∧ H.T2 = T ∧ H.Lw = Lw ∧ H.CT2 = CT2 ∧ H.QS = 2 ^ (R.e + 2) := by
  obtain ⟨H, rfl, rfl, hQS, -, -, -, hPS, hEx, s, hs, hgs⟩ := Formalism.HC.exists_hostAx R.toFrame hinj he hyp
  have hcm : H.cmType.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [H.der.cmType.2.1]
    have := R.ord_pos
    omega
  obtain ⟨𝔟, h1, h2, h4⟩ := H.der.principal
  refine ⟨{ toHostAx := H, flPS := hPS, sqq := s, sqq_sq := hs, gal_sqq := hgs, QS_exact := hEx
            QS_le := by rw [hQS]; exact Formalism.HC.D7.qs_le R.toFrame hinj he
            o_pow := ho, q_ne_three := h3, qd_big := hbig, splitBound := B, split_small := hsp
            small_le := fun l hl h2 hd => by
              rw [hQS] at hd
              exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow hd)) h2
            φ₀ := hcm.some, φ₀_mem := hcm.some_mem,
            𝔟 := 𝔟, 𝔟_spec := ⟨h1, h2⟩, 𝔟_stable := h4, levelPrimes := {g 0, g 1, p, p', q0}, g := g, g_prime := hg, g_ne := hne,
            g_level := by intro i; fin_cases i <;> simp
            pde := p, pde' := p', pde_prime := hp, pde'_prime := hp', pde_ne := hpp, pde_level := by simp
            pde_mod := hm, pde_ne_g := hpg, ccK := ⊤, ccK_ne_bot := top_ne_bot,
            ccK_primitive := fun m hm => top_primitive m hm
            ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
            ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
            ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
            level_coprimeS := fun l hl => by
              rw [hQS]
              exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 (Nat.odd_iff.2 (hodd l hl)))
            TT := ∅, T2 := T, u0 := 0, Lw := Lw, two_le_Lw := hL, second_set_range := hT, second_set_no_relation := hT', CT2 := CT2 },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hQS⟩

theorem log_le_rpow_eventually (eps C : ℝ) (he : 0 < eps) (hC : 0 < C) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → C * Real.log x ≤ x ^ eps := by
  have h := (isLittleO_log_rpow_atTop he).bound (inv_pos.2 hC)
  obtain ⟨x0, h0⟩ := Filter.eventually_atTop.1 h
  refine ⟨max x0 1, fun x hx => ?_⟩
  have h1 := h0 x (le_of_max_le_left hx)
  have hx1 : 1 ≤ x := le_of_max_le_right hx
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg (by positivity)] at h1
  calc C * Real.log x ≤ C * (C⁻¹ * x ^ eps) := by gcongr
    _ = x ^ eps := by field_simp

theorem qd_big (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (q d : ℕ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → Rowq s.x s.eps R.n q d →
      (4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d) ∧ q ≠ 3 := by
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 814 1 he one_pos
  refine ⟨max (max x1 x2) 5, fun s R q d hs hx hR hrow => ?_⟩
  have hx5 : 5 ≤ s.x := le_of_max_le_right hx
  have hx0 : 0 < s.x := by linarith
  obtain ⟨-, -, hr, -, -, -, -, -, -, -, -, -, -, ht, -⟩ :=
    h1 s R hs (le_of_max_le_left (le_of_max_le_left hx)) hR
  have h814 := (h2 s hs (le_of_max_le_right (le_of_max_le_left hx))).1
  have hX1 : s.x ^ (814 : ℝ) ≤ GlobalTheoryTheory.X1 s.x s.eps := by
    refine h814.trans (Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le ?_))
    have := s.eps_pos; linarith
  have hlog : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  have hX2 : GlobalTheoryTheory.X1 s.x s.eps ≤ GlobalTheoryTheory.X2 s.x s.eps := by
    refine Real.exp_le_exp.2 (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog))
  have hsq : s.x ^ (407 : ℝ) ≤ Real.sqrt (GlobalTheoryTheory.X1 s.x s.eps) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num at hX1 ⊢
    exact hX1
  have h406 : (R.t : ℝ) * R.r ≤ s.x ^ (406 : ℝ) := by
    rw [show (406 : ℝ) = 401 + 5 by norm_num, Real.rpow_add hx0]
    gcongr
  have h1' : 1 ≤ s.x ^ (406 : ℝ) := Real.one_le_rpow s.one_lt_alt.le (by norm_num)
  have h407 : 5 * s.x ^ (406 : ℝ) ≤ s.x ^ (407 : ℝ) := by
    rw [show (407 : ℝ) = 1 + 406 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    gcongr
  have hb : ((4 * R.t * R.r + 1 : ℕ) : ℝ) ≤ Real.sqrt (GlobalTheoryTheory.X1 s.x s.eps) := by
    push_cast; linarith
  have hq := hrow.2.2.1
  have hd := (Real.sqrt_le_sqrt hX2).trans_lt hrow.2.2.2.2.2.2.1
  refine ⟨⟨by exact_mod_cast hb.trans_lt hq, by exact_mod_cast hb.trans_lt hd⟩, ?_⟩
  rintro rfl
  push_cast at hq
  linarith

theorem cond_pow_lt (eps C : ℝ) (he : 0 < eps) (hC : 1 ≤ C) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (q d : ℕ),
    s.eps = eps → x0 ≤ s.x → Rowq s.x s.eps R.n q d →
      (4 * (R.n : ℝ) * q * d) ^ C < ((R.k : ℝ) * s.b) ^ 8 := by
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (2 * C) 1 he one_pos
  refine ⟨x2, fun s R q d hs hx hrow => ?_⟩
  obtain ⟨-, -, h3, -, -, -, h7⟩ := h2 s hs hx
  rw [Real.rpow_one] at h3 h7
  have hxc : 1 ≤ s.x ^ (2 * C) := Real.one_le_rpow s.one_lt_alt.le (by linarith)
  have hn : (0 : ℝ) < R.n := by exact_mod_cast R.ord_pos
  have hq : (0 : ℝ) < q := by exact_mod_cast hrow.1.pos
  have hd : (0 : ℝ) < d := by exact_mod_cast hrow.2.2.2.2.1.pos
  have hN : (0 : ℝ) < 4 * (R.n : ℝ) * q * d := by positivity
  have hlog := hrow.2.2.2.2.2.2.2.2.2.2
  have a1 : (4 * (R.n : ℝ) * q * d) ^ C ≤ Real.exp (2 * C * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) := by
    rw [Real.rpow_def_of_pos hN]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hX : 0 < s.X' := Real.exp_pos _
  have a2 : Real.exp (2 * C * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤ s.X' :=
    (le_mul_of_one_le_right (Real.exp_pos _).le hxc).trans h7
  have a3 : s.X' ≤ s.b := (le_mul_of_one_le_left hX.le hxc).trans h3
  have hb : 1 < s.b := by
    have : 0 < s.L := Real.rpow_pos_of_pos (by have := s.one_lt_alt; linarith) _
    exact Real.one_lt_exp_iff.2 this
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have a4 : s.b ≤ R.k * s.b := le_mul_of_one_le_left (by linarith) hk
  have a5 : (R.k : ℝ) * s.b < ((R.k : ℝ) * s.b) ^ 8 := lt_self_pow₀ (by linarith) (by norm_num)
  linarith

theorem exists_hostGood (hThin : ThinChoice) (hNP : NormPrimes) (hSP : SmallPrimeOne) (hTops : TopsChoice) (eps C5 : ℝ)
    (he : 0 < eps) (he' : eps < 1 / 52) (hC5 : 0 < C5) :
    ∃ CT2 C8 c6 Cb x0 : ℝ, 1 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧ ∀ (s : Scale) (R : Ranks) (q d : ℕ), s.eps = eps → x0 ≤ s.x → s.J ≤ 4 →
      RankVal s R → 2 ≤ R.e → R.toFrame = Formalism.HC.cyclicFrame R.e → Rowq s.x s.eps R.n q d → QDq s.x s.eps C5 q d →
      Boxq s.x s.eps q d →
      ∃ (H : Host R) (q0 : ℕ), H.q = q ∧ H.d = d ∧ H.QS = 4 * R.n ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧
        R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps)) := by
  obtain ⟨c6, hc6, hThin⟩ := hThin eps he he'
  obtain ⟨xb, hThin⟩ := hThin 4
  obtain ⟨Cb, xc, hCb, hTops⟩ := hTops eps 4 he he'
  obtain ⟨C8, hC8, hAux⟩ := GlobalTheory.T.exists_primes_in_progression_bounded hSP
  obtain ⟨xd, hG⟩ := GlobalTheory.T.exists_two_large_norm_one_primes hNP eps he he'
  obtain ⟨CT2, hT⟩ := GlobalTheory.T.exists_noRel_finset_card_ge
  obtain ⟨xe, hT⟩ := hT eps 4 he he'
  obtain ⟨xf, hlog⟩ := log_le_rpow_eventually eps C5 he hC5
  obtain ⟨xg, hbig⟩ := qd_big eps he he'
  obtain ⟨xh, hlt⟩ := cond_pow_lt eps C8 he hC8
  refine ⟨CT2, max C8 4, c6, Cb, max (max xb (max xc xd)) (max (max xe xf) (max xg xh)), le_max_of_le_left hC8, hc6, hCb,
    fun s R q d hs hx hJ hR h2e hφ hrow hqd hbox => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hb, hc, hd⟩, ⟨hxe, hf⟩, hg, hh⟩ := hx
  have hfr : ∀ (φ : Formalism.HC.Frame) (e : ℕ), φ = Formalism.HC.cyclicFrame e → Function.Injective φ.h ∧ φ.o = 1 ∧ φ.ord = 2 ^ e := by
    rintro _ e rfl
    exact ⟨Formalism.HC.frameCyc_h_injective e 1, Formalism.HC.cyclicFrame_index e, rfl⟩
  obtain ⟨hinj, ho1, hord⟩ := hfr _ _ hφ
  have ho4 : (R.o : ℝ) ≤ 4 := by rw [ho1]; norm_num
  have hn : 1 ≤ R.n := R.ord_pos
  have hq8 : q % 8 = 3 := hrow.2.1
  have hd16 : d % 16 = 7 := hrow.2.2.2.2.2.1
  have hyp : Formalism.FrobeniusOrbits.HostHyp q d :=
    ⟨hrow.1, hrow.2.2.2.2.1, hq8, hd16, by rw [← kronSym_of_odd _ (by omega)]; exact hrow.2.2.2.2.2.2.2.2.1⟩
  have hN : 30 ≤ 4 * R.n * q * d := by
    have : 4 * 1 * 3 * 7 ≤ 4 * R.n * q * d := by gcongr <;> omega
    omega
  have hd100 : 100 ≤ d := by
    have h1 := (hbig s R q d hs hg hR hrow).1.2
    have h2 := R.rank_add_five_le
    have h3 := R.m_add_three_le_k
    have h4 := R.two_le_m
    have hr : 6 ≤ R.r := by unfold Ranks.r; omega
    have ht : 11 ≤ R.t := by omega
    have h5 : 4 * 11 * 6 ≤ 4 * R.t * R.r := by gcongr
    omega
  have hmod := modRow_of_rowq (pairWin_self s) hn hd100 hrow
  obtain ⟨p, p', q0, hp, hp', hq0, hpp, hq0p, hq0p', mp, mp', mq0, lp, lp', lq0⟩ := hAux _ hN
  have hmono : ((4 * R.n * q * d : ℕ) : ℝ) ^ C8 ≤ ((4 * R.n * q * d : ℕ) : ℝ) ^ max C8 4 :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ 4 * R.n * q * d)) (le_max_left _ _)
  have kp := lp.trans hmono
  have kp' := lp'.trans hmono
  have kq0 := lq0.trans hmono
  push_cast at lp lp' lq0
  obtain ⟨g, hgi, hg01, hdisj⟩ := hG s R _ d hs hd hR hmod
  obtain ⟨T, t1, t2, t3, t4, t5, t6⟩ := hT s R hs hxe hR ho4
  have hlt' := hlt s R q d hs hh hrow
  have m15 : ∀ a : ℕ, a % (15 * (4 * R.n * q * d)) = 1 → a % 15 = 1 ∧ a % (4 * R.n * q * d) = 1 := fun a h =>
    mod_of_mod_lcm (by omega) (mod_lcm_of_mod_mul (by omega) h)
  have hodd : ∀ l ∈ ({g 0, g 1, p, p', q0} : Finset ℕ), l % 2 = 1 := by
    have o1 : ∀ a : ℕ, a % (4 * R.n * q * d) = 1 → a % 2 = 1 := fun a h => by
      rw [← Nat.mod_mod_of_dvd a (⟨2 * R.n * q * d, by ring⟩ : 2 ∣ 4 * R.n * q * d), h]
    have o2 : ∀ i, g i % 2 = 1 := fun i => by
      have h1 : p < g i := by exact_mod_cast (lp.trans_lt hlt').trans_le (hgi i).2.1
      have h2 := hp.two_le
      exact ((hgi i).1.eq_two_or_odd).resolve_left (by omega)
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl
    exacts [o2 0, o2 1, o1 _ (m15 _ mp).2, o1 _ (m15 _ mp').2, o1 _ mq0]
  obtain ⟨H0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := exists_host R q d ⌊s.x ^ (s.ez / 5)⌋₊ hyp
    (hbig s R q d hs hg hR hrow).1 (hbig s R q d hs hg hR hrow).2 h2e hinj
    (by rw [ho1, one_pow]; exact Nat.one_le_two_pow)
    (fun l hl h2 hle => by
      rw [← kronSym_of_odd _ (fun h => h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).1 h).symm)]
      refine hrow.2.2.2.2.2.2.2.2.2.1 l hl (((Nat.le_floor_iff ?_).1 hle).trans
        ((pairWin_self s).rpow_ez_le (by norm_num)))
      have := s.one_lt_alt
      positivity)
    g p p' q0 (fun i => (hgi i).1) hg01 hp hp' hpp ⟨(m15 p mp).1, (m15 p' mp').1⟩
    (fun i => ⟨fun h => by have := (hgi i).2.1; rw [← h] at this; linarith,
      fun h => by have := (hgi i).2.1; rw [← h] at this; linarith⟩)
    hodd T (Lwv s) t6 t1 t2 CT2
  subst e1 e2 e4 e5 e6 e9 e11
  have hQS : H0.QS = 4 * R.n := by
    rw [e12, show R.n = 2 ^ R.e from hord]; ring
  have hQR : (H0.QS : ℝ) = 4 * R.n := by exact_mod_cast hQS
  rw [← hQS] at hN hgi m15 mp mp' mq0 kp kp' kq0
  push_cast at kp kp' kq0
  obtain ⟨TT, tt1, tt2, hbad, hsh⟩ := hTops s R H0 hs hc hR hJ ho4 e3.ge
  have hnorm := fun i => GlobalTheory.T.norm_one_prime_elements R H0 (H0.QS * H0.q * H0.d) (H0.g i) (by omega) (hgi i).2.2.2
  have hgm : ∀ i, H0.g i % (H0.QS * H0.q * H0.d) = 1 := fun i =>
    (hnorm i).2.trans (Nat.mod_eq_of_lt (by omega))
  have hsplit := GlobalTheory.HostSplit.split_of_one_mod R H0
  have hpr : PairRow s.x s.eps H0 := by
    rw [pairRow_iff_rowq, hQS, Nat.mul_div_cancel_left _ (by norm_num)]
    exact hrow
  have hbH : BoxH { H0 with TT := TT } s.x s.eps := UpperTheory.box_bound_for_host R _ _ _ hinj e12 hbox
  have hcond : Real.log ((H0.QS : ℝ) * H0.q * H0.d) ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    have := hmod.2.2.2.2.2
    rw [← hQS] at this
    push_cast at this
    exact this
  have h4 : (4 : ℝ) ≤ max C8 4 := le_max_right _ _
  refine ⟨{ H0 with TT := TT }, q0, rfl, rfl, hQS, rfl,
    ⟨⟨⟨s.x, pairWin_self s, hpr⟩, ⟨tt1, tt2⟩, t4, ⟨kp, kp'⟩, fun i => ⟨(hgi i).2.1, (hgi i).2.2.1⟩, e10, e8, e3.ge,
      hJ.trans h4, ho4.trans h4, hQR.trans_le (mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _))⟩,
    ⟨fun i => ?_, hgm, ⟨?_, ?_⟩, fun l hl => ?_⟩, ?_, ?_, hqd, ⟨s.x, pairWin_self s, hpr, hbox, hbH⟩, ?_,
    hThin s R _ hs hb hR ho4 hQR.le hcond hbH.realBox, hbad, hdisj,
    fun i => (hnorm i).1, ⟨mod_lcm_of_mod_mul H0.condN_pos mp, mod_lcm_of_mod_mul H0.condN_pos mp'⟩,
    ⟨hq0, mq0, kq0, hq0p, hq0p'⟩, e7⟩, hsh⟩
  · obtain ⟨π, h1, h2, -⟩ := (hnorm i).1
    exact ⟨π, h1, h2⟩
  · exact (GlobalTheory.HostSplit.ncard_placesOver H0.E hp).symm.trans (hsplit _ hp (m15 _ mp).2).1
  · exact (GlobalTheory.HostSplit.ncard_placesOver H0.E hp').symm.trans (hsplit _ hp' (m15 _ mp').2).1
  · have hl' : l ∈ H0.levelPrimes := hl
    rw [e7] at hl'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with rfl | rfl | rfl | rfl | rfl
    · exact (hsplit _ (hgi 0).1 (hgm 0)).2
    · exact (hsplit _ (hgi 1).1 (hgm 1)).2
    · exact (hsplit _ hp (m15 _ mp).2).2
    · exact (hsplit _ hp' (m15 _ mp').2).2
    · exact (hsplit _ hq0 mq0).2
  · rw [← e10] at t3
    exact t3
  · rw [← e10] at t5
    exact t5
  · refine (abs_dlogH_le { H0 with TT := TT } hqd).trans ?_
    rw [hs]
    exact hlog s.x hf

theorem hostEx : QDChoice → ThinChoice → NormPrimes → SmallPrimeOne → TopsChoice → HostEx := by
  intro hQD hThin hNP hSP hTops
  refine ⟨2, by norm_num, fun eps he he' => ?_⟩
  obtain ⟨C5, xa, hC5, hQD⟩ := hQD eps he he'
  obtain ⟨CT2, C8, c6, Cb, xb, hC8, hc6, hCb, h⟩ := exists_hostGood hThin hNP hSP hTops eps C5 he he' hC5
  obtain ⟨xc, hRk⟩ := exists_ranks_cyclic_frame eps he he'
  refine ⟨CT2, C8, C5, c6, Cb, max xa (max xb xc), hC8, hC5, hc6, hCb, Scales.univ 2 1 le_rfl, fun s hs hx hS => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨R, hR, h2e, hφ⟩ := hRk s hs hx.2.2
  obtain ⟨q, d, hrow, hqd, hbox⟩ := hQD s.x hx.1 R.n R.ord_pos (hs ▸ hR.1.2)
  rw [← hs] at hrow hqd hbox
  obtain ⟨H, q0, -, -, -, h1, h2, -⟩ := h s R q d hs hx.2.1 (by rw [Scales.mem_univ.1 hS]; norm_num) hR h2e hφ hrow hqd hbox
  exact ⟨R, H, q0, hR, h1, h2, trivial⟩

end GlobalTheory.EX.HostExist
