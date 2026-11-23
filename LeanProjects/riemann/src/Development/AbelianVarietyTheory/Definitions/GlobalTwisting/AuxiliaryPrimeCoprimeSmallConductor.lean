import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitConstantsParameterConditionsLarge
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InjectiveOfOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt

noncomputable section

namespace GlobalTheory.EX.DC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem auxiliaryPrime_le_conductor_rpow {A C : ℝ} (hA : 1 ≤ A) (hS : ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A)
    {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (h1 : (H.pde : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C)
    (h2 : (H.pde' : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C) :
    (q0H H : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ ((3 + 2 * C) * A) := by
  obtain ⟨p, hp, hm, hle⟩ := hS _ (one_lt_rPrH_mul H)
  have hq : (q0H H : ℝ) ≤ p := by exact_mod_cast globalTwisting_le_fact H hc hp hm
  have hN : 2 ≤ H.QS * H.q * H.d := by
    have a1 := H.QS_pos
    have a2 := H.hyp.1.two_le
    have a3 := H.hyp.2.1.pos
    have : 1 * 2 * 1 ≤ H.QS * H.q * H.d := by gcongr <;> omega
    omega
  have e : ((H.QS : ℝ) * H.q * H.d) = ((H.QS * H.q * H.d : ℕ) : ℝ) := by push_cast; ring
  rw [e] at h1 h2 ⊢
  have a2 : 0 < H.pde - 1 := Nat.sub_pos_of_lt H.pde_prime.one_lt
  have a3 : 0 < H.pde' - 1 := Nat.sub_pos_of_lt H.pde'_prime.one_lt
  have hr : rPrH H ≤ 2 * (H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1)) := by
    have hM : 0 < H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) a2) a3
    obtain ⟨r, hr, hr1, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul _ hM.ne'
    refine (rPrH_le H hr ?_).trans hr2
    rw [hc, Ideal.absNorm_top, mul_one]
    exact Nat.not_dvd_of_pos_of_lt hM hr1
  generalize H.QS * H.q * H.d = N at *
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hr' : rPrH H ≤ N * (N * H.pde * H.pde') := hr.trans (by gcongr <;> omega)
  have hr'' : (rPrH H : ℝ) ≤ N * (N * H.pde * H.pde') := by exact_mod_cast hr'
  have hb : ((rPrH H * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (3 + 2 * C) := by
    have : (N : ℝ) ^ (3 + 2 * C) = N * (N * N ^ C * N ^ C) * N := by
      rw [show 3 + 2 * C = ((3 : ℕ) : ℝ) + C + C by push_cast; ring, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
      ring
    rw [this, Nat.cast_mul]
    refine mul_le_mul_of_nonneg_right (hr''.trans ?_) hN0.le
    gcongr
  rw [Real.rpow_mul hN0.le]
  exact hq.trans (hle.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by linarith)))

theorem auxiliaryPrime_coprime_smallConductor {R : Ranks} (H : Host R) : Nat.Coprime (q0H H) H.QS := by
  have h1 : Nat.Coprime (q0H H) (H.QS * H.q * H.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, mod_cond H, Nat.gcd_one_left]
  exact h1.coprime_dvd_right ⟨H.q * H.d, by ring⟩

def relevel {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (q0 : ℕ)
    (hq : Nat.Coprime q0 H.QS := by exact GlobalTheory.EX.DC.auxiliaryPrime_coprime_smallConductor _) : Host R :=
  { H with
    levelPrimes := {H.g 0, H.g 1, H.pde, H.pde', q0}
    g_level := by intro i; fin_cases i <;> simp
    pde_level := by simp
    ccK_coprime := fun p _ => by rw [hc, Ideal.absNorm_top]; exact Nat.coprime_one_left p
    level_coprimeS := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h | h <;> rw [h]
      · exact H.level_coprimeS _ (H.g_level 0)
      · exact H.level_coprimeS _ (H.g_level 1)
      · exact H.level_coprimeS _ H.pde_level.1
      · exact H.level_coprimeS _ H.pde_level.2
      · exact hq }

theorem hostExQW_of_hostExW (hS : SmallPrimeOne) {la : ℝ} {P : HostReq}
    (hP : ∀ (c : ℝ) (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (hc : H.ccK = ⊤), P c s R H q0 →
      P c s R (relevel H hc (q0H H)) (q0H H))
    (hH : HostExW la P) : HostExQW la P := by
  obtain ⟨A, hA, hS⟩ := hS
  intro eps he he'
  obtain ⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, hH⟩ := hH eps he he'
  have hC : C8 ≤ (3 + 2 * C8) * A := by nlinarith
  refine ⟨CT2, (3 + 2 * C8) * A, C5, c6, Cb, x0, h8.trans hC, h5, h6, hb, S, fun s hs hx hm => ?_⟩
  obtain ⟨R, H, q0, hR, hT, ⟨hv, har, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, -, hlev⟩, hp⟩ := hH s hs hx hm
  have hc : H.ccK = ⊤ := hv.2.2.2.2.2.2.1
  have hv' : HostVal s ((3 + 2 * C8) * A) (relevel H hc (q0H H)) := hv.mono hC
  have hq := auxiliaryPrime_le_conductor_rpow hA hS H hc hv.2.2.2.1.1 hv.2.2.2.1.2
  have har' : HostArith (relevel H hc (q0H H)) := ?_
  · exact ⟨R, relevel H hc (q0H H), q0H H, hR, hT, ⟨hv', har', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
      ⟨(globalTwisting_spec_fact H).1, mod_cond H, hq, q0H_ne_pde_and_ne_pde' H⟩, rfl⟩, globalTwisting_congr_fact _ rfl rfl rfl rfl rfl rfl, hP _ _ _ _ _ hc hp⟩
  refine ⟨har.1, har.2.1, har.2.2.1, fun l hl => ?_⟩
  have hl' : l ∈ ({H.g 0, H.g 1, H.pde, H.pde', q0H H} : Finset ℕ) := hl
  show H.cls l = .splitK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
  rcases hl' with h | h | h | h | h <;> rw [h]
  · exact har.2.2.2 _ (H.g_level 0)
  · exact har.2.2.2 _ (H.g_level 1)
  · exact har.2.2.2 _ H.pde_level.1
  · exact har.2.2.2 _ H.pde_level.2
  · exact (GlobalTheory.HostSplit.split_of_one_mod R H _ (globalTwisting_spec_fact H).1 (mod_cond H)).2

theorem hostExQ_of_hostEx (hS : SmallPrimeOne) (hH : HostEx) : HostExQ :=
  let ⟨la, h1, h2⟩ := hH
  ⟨la, h1, HostExW.imp (hostExQW_of_hostExW hS (fun _ _ _ _ _ _ h => h) h2) fun _ _ _ _ _ h => h.1⟩

theorem firstTypePrime_lt_rowPrime (D : D7) (u : D.what₂.Word) : D.host.g 0 < (D.mem u).A.T := by
  have h := (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd D.host.d _ _ (by have := D.host.hyp.2.2.2.1; omega)
    ((GlobalTheory.Mem.An.normOne_iff_host D.R D.host _ _).2 (D.T_norm u))).1
  have h' : (D.mem u).A.T ≡ 1 [MOD D.host.g 0] := Nat.ModEq.of_dvd (Dvd.dvd.mul_left ⟨D.host.g 0 * D.host.g 1 ^ 2, by ring⟩ _) h
  have h1 := (D.mem u).A.T_prime.one_lt
  have := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' h1.le).1 h'.symm)
  omega

theorem ObjC.and_q0Pt {Q : PtProp} (h : ObjC Q) : ObjC (Q.and twistingGlobalPointProp) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  obtain ⟨c1', hP⟩ := explicitConstants_parameterConditions_large eps a1 a3 C b1
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hP⟩ := hP cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch ((le_max_left _ _).trans hch)
  obtain ⟨x1, hP⟩ := hP ch ((le_max_right _ _).trans hch)
  obtain ⟨x2, hq⟩ := small_prime_lt eps C8 a1 a4
  obtain ⟨x3, hJ⟩ := GlobalTheory.ClassDuty.windowsAt_of eps a1 a3 C b1
  refine ⟨max (max x0 x1) (max x2 x3), fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  simp only [max_le_iff] at d2
  obtain ⟨p, e1, e2, e3, e4, e5, e6⟩ := h s R H q0 a b M c u0 d1 d2.1.1 d3 d4 d5 d0 d6 d7 d8 d9
  refine ⟨p, e1, e2, e3, e4, e5, e6, ?_⟩
  subst e1
  show GlobalTwistingFacts p.L
  obtain ⟨hv, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hle, -⟩, hlev⟩ := d5
  have eq0 : q0Av p.D = q0 := (eq_of_from p e4 e2.host.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1).trans d0.symm
  have hX : (q0Av p.D : ℝ) < p.L.sc.X' := by
    rw [eq0]
    exact hq _ _ q0 d1 d2.2.1 (by exact_mod_cast cond_pos H) hv.log_cond_le hle
  obtain ⟨P, -⟩ := hP _ _ d1 d2.1.2 e2 e3
  have hXb := X'_le_b p.L.sc
  have hs := globalTwisting_spec_fact p.D.host
  have hg : ∀ j, q0Av p.D < p.D.host.g j := by
    intro j
    have hg := (e2.host.2.2.2.2.1 j).1
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast (show (q0Av p.D : ℝ) < p.D.host.g j by linarith)
  refine ⟨?_, hs.1, hs.2.1, ?_, hX, hX.le.trans (hJ cD ch _ _ d1 d2.2.2 e2 P).2, (q0H_ne_pde_and_ne_pde' _).1, (q0H_ne_pde_and_ne_pde' _).2,
    fun j => (hg j).ne, fun u => ((hg 0).trans (firstTypePrime_lt_rowPrime _ u)).ne⟩
  · rw [eq0]
    exact e4.2.2.2.2.2.2.2.2.1 (by rw [hlev]; simp)
  · rw [Real.log_le_iff_le_exp (by exact_mod_cast hs.1.pos)]
    exact hX.le.trans hXb

theorem objC_withObj_iff (Q : PtProp) : ObjC (withObj Q) ↔ ObjC (Q.and (TamePt.and (MinkPt.and TwPt))) :=
  ⟨fun h => h.imp fun _ _ hp => ⟨hp.1.1, hp.2⟩, fun h => h.and_q0Pt.imp fun _ _ hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩⟩

theorem hostWW_of_hostExQW_weightEx {la : ℝ} {P : HostReq} (hH : HostExQW la P) (hW : WeightEx) : HostWW la P := by
  refine ⟨1, one_pos, fun eps he _ he1 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, xH, h8, h5, h6, hb, S, hH⟩ := hH eps he he1
  obtain ⟨KW, hW⟩ := hW eps C8 he he1
  refine ⟨CT2, C8, C5, c6, Cb, KW, h8, h5, h6, hb, fun C hC _ _ hL => ⟨0, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩⟩
  obtain ⟨xW, hW⟩ := hW C hC hL cD ch hcD
  refine ⟨max xH xW, S, fun s hs hx hm => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨R, H, q0, hRV, hT, hG, hq, hp⟩ := hH s hs hx.1 hm
  obtain ⟨a, b, h0, h1, h2⟩ := hW s R H hs hx.2 hRV hG.1
  exact ⟨R, H, q0, a, b, hRV, hT, hG, hq, h0, h1, h2, hp⟩

theorem hostW_of_hostExQ_weightEx (hH : HostExQ) (hW : WeightEx) : HostW :=
  let ⟨la, h1, h2⟩ := hH
  ⟨la, h1, hostWW_of_hostExQW_weightEx (HostExW.imp h2 fun _ _ _ _ _ h => ⟨h, trivial⟩) hW⟩

theorem not_objC_false (hHost : HostW) : ¬ ObjC (fun _ _ _ _ _ _ _ _ _ => False) := by
  rintro ⟨εO, hεO, hObj⟩
  obtain ⟨la, hla, εH, hεH, hHost⟩ := hHost
  obtain ⟨eps, he, e1, e2, he1⟩ : ∃ eps : ℝ, 0 < eps ∧ eps ≤ εH ∧ eps ≤ εO ∧ eps < 1 / 52 :=
    ⟨min (min εH εO) (1 / 53), by positivity, (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨CT2, C8, C5, c6, Cb, KW, h8, -, -, -, hHost⟩ := hHost eps he e1 he1
  obtain ⟨KO, hObj⟩ := hObj eps C8 C5 c6 Cb he e2 he1 h8
  obtain ⟨C, hC, hT, hP, hLW, hLO, -⟩ := exists_std_large KW KO CT2 C8 h8
  obtain ⟨c1, hObj⟩ := hObj C hC hP hLO
  obtain ⟨c1', hHost⟩ := hHost C hC hT hP hLW
  obtain ⟨c2, hObj⟩ := hObj _ (le_max_left c1 c1')
  obtain ⟨c2', hHost⟩ := hHost _ (le_max_right c1 c1')
  obtain ⟨xO, hObj⟩ := hObj _ (le_max_left c2 c2')
  obtain ⟨xH, S, hHost⟩ := hHost _ (le_max_right c2 c2')
  have hmid := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨xC, hCode⟩ := exists_injective_words eps C.CGam C.P.CF he he1
    (zero_le_one.trans (hmid _ (by simp [FC.cMid]))) (zero_le_one.trans (hmid _ (by simp [FC.cMid])))
  obtain ⟨s, hs, hx, hm⟩ := S.exists_mem hla.le he he1 (max xO (max xH xC))
  simp only [max_le_iff] at hx
  obtain ⟨R, H, q0, a, b, hRV, hHT, hH, hq, -, hWin, -⟩ := hHost s hs hx.2.1 hm
  obtain ⟨c, hc, -⟩ := hCode s R hs hx.2.2 hRV
  obtain ⟨p, -, -, -, -, -, hp⟩ := hObj s R H q0 a b _ c 0 hs hx.1 hRV (hHT.trans hT.symm) hH hq hWin rfl hc
    R.ord_pos
  exact hp

theorem not_kitC_false : ¬ KitC (fun _ _ _ _ _ _ _ _ _ => False) := by
  rintro ⟨la, hla, ε0, h0, h⟩
  obtain ⟨eps, he, e1, he1⟩ : ∃ eps : ℝ, 0 < eps ∧ eps ≤ ε0 ∧ eps < 1 / 52 :=
    ⟨min ε0 (1 / 53), by positivity, min_le_left _ _, (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨CT2, C8, K0, h8, h⟩ := h eps he e1 he1
  obtain ⟨C, hC, hT, hP, hL, -⟩ := exists_std_large K0 K0 CT2 C8 h8
  obtain ⟨c1, h⟩ := h C hC hT hP hL
  obtain ⟨c2, h⟩ := h c1 le_rfl
  obtain ⟨C5, Cb, x0, -, -, S, h⟩ := h c2 le_rfl
  obtain ⟨s, hs, hx, hm⟩ := S.exists_mem hla.le he he1 x0
  obtain ⟨k, hk⟩ := h s hs hx hm
  exact k.ne.elim fun i => (hk i).1

end GlobalTheory.EX.DC

end
