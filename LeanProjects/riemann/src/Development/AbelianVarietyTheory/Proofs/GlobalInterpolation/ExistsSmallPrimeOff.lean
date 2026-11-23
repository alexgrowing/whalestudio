import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHcParamOfCode
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitExOfHostWeightObj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem leastOff_prime_le {K : ℕ} (hK : 0 < K) : (leastOff K).Prime ∧ leastOff K ≤ K + 1 := by
  have hp : (K + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hm : (K + 1).minFac ∈ {r : ℕ | r.Prime ∧ ¬ r ∣ K} := by
    refine ⟨hp, fun h => hp.one_lt.ne' ?_⟩
    exact Nat.dvd_one.1 ((Nat.dvd_add_right h).1 (Nat.minFac_dvd _))
  exact ⟨(Nat.sInf_mem ⟨_, hm⟩).1, (Nat.sInf_le hm).trans (Nat.minFac_le (by omega))⟩

theorem exists_small_prime_off (h : SmallPrimeOne) (C8 : ℝ) (h8 : 1 ≤ C8) : ∃ C9 : ℝ, 1 ≤ C9 ∧ ∀ N p p' : ℕ, 2 ≤ N →
    p.Prime → p'.Prime → (p : ℝ) ≤ (N : ℝ) ^ C8 → (p' : ℝ) ≤ (N : ℝ) ^ C8 →
    ∃ q1 : ℕ, q1.Prime ∧ q1 % N = 1 ∧ q1 ≠ p ∧ q1 ≠ p' ∧ q1 % (leastOff (N * (p - 1) * (p' - 1)) * N) = 1 ∧
      (q1 : ℝ) ≤ (N : ℝ) ^ C9 := by
  obtain ⟨A, hA, h⟩ := h
  refine ⟨(2 * (1 + 2 * C8)) * A, by nlinarith, fun N p p' hN hp hp' hb hb' => ?_⟩
  have h2 := hp.two_le
  have h2' := hp'.two_le
  obtain ⟨x, rfl⟩ : ∃ x, p = x + 1 := ⟨p - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, p' = y + 1 := ⟨p' - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hK : 0 < N * x * y := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  obtain ⟨hr, hrle⟩ := leastOff_prime_le hK
  set r := leastOff (N * x * y) with hrdef
  have hr2 := hr.two_le
  have hrN : 1 < r * N := by nlinarith
  have hM : 2 ≤ r * N * (x + 1) * (y + 1) := by
    have : r * N ≤ r * N * (x + 1) * (y + 1) := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  obtain ⟨q1, hq, hmod, hle⟩ := h _ hM
  have key : ∀ m : ℕ, 1 < m → m ∣ r * N * (x + 1) * (y + 1) → q1 % m = 1 := fun m hm hdv => by
    rw [← Nat.mod_mod_of_dvd q1 hdv, hmod, Nat.mod_eq_of_lt hm]
  refine ⟨q1, hq, key N (by omega) ⟨r * (x + 1) * (y + 1), by ring⟩, ?_, ?_,
    key _ hrN ⟨(x + 1) * (y + 1), by ring⟩, hle.trans ?_⟩
  · rintro rfl
    have := key (x + 1) (by omega) ⟨r * N * (y + 1), by ring⟩
    simp at this
  · rintro rfl
    have := key (y + 1) (by omega) ⟨r * N * (x + 1), by ring⟩
    simp at this
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    have e1 : r ≤ N * (x + 1) * (y + 1) := by nlinarith [Nat.zero_le (N * x), Nat.zero_le (N * y)]
    have e2 : ((N * (x + 1) * (y + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 + 2 * C8) := by
      rw [show 1 + 2 * C8 = 1 + C8 + C8 by ring, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one,
        Nat.cast_mul, Nat.cast_mul]
      gcongr
    have e3 : (r : ℝ) ≤ (N : ℝ) ^ (1 + 2 * C8) := le_trans (by exact_mod_cast e1) e2
    rw [two_mul, Real.rpow_add hN0,
      show r * N * (x + 1) * (y + 1) = r * (N * (x + 1) * (y + 1)) by ring, Nat.cast_mul]
    gcongr

theorem chOK_of_host_field : SmallPrimeOne → ∀ (eps C5 c6 Cb cD ch : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 → HostGood s C.P.Cpde C5 c6 Cb H q0 → WinOK s C.GK H a b → M = ⌈3 * GamS C s R ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c → u0 < R.n → ∃ (H' : Host R) (q1 : ℕ) (hcW : Fin M → Tau R → HCParam R) (w0 : Fin M) (h1 : _) (h2 : _) (h3 : _) (h4 : _) (h5 : _) (h6 : _) (h7 : _) (h8 : _), ChOK s C cD ch (@PreCh.mk R H' h1 h2 h3 (Fin M) _ w0 hcW h4 h5 h6 h7 h8) q1 a b c ∧ H'.TT = H.TT ∧ H'.T2 = H.T2 ∧ H'.q = H.q ∧ H'.d = H.d ∧ H'.g = H.g ∧ H'.pde = H.pde ∧ H'.pde' = H.pde' ∧ H.levelPrimes ⊆ H'.levelPrimes ∧ H'.u0.val = u0 ∧ (∀ l, hPH H' l = hPH H l) ∧ H'.toHostAx = H.toHostAx := by
  intro hSP eps C5 c6 Cb cD ch C he he1 hC hcD hch
  have h8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨C9, h9, hq1⟩ := exists_small_prime_off hSP _ h8
  obtain ⟨x1, hx1⟩ := small_prime_lt eps _ he h8
  obtain ⟨x2, hx2⟩ := small_prime_lt eps _ he h9
  obtain ⟨x3, hx3⟩ := exists_hc_family eps cD ch C.P.Cpde he he1 hcD hch
  refine ⟨max x1 (max x2 x3), fun s R H q0 a b M c u0 hs hx hR hT hH hW hM hc hu => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hv, har, hT2, hT3, -, -, hdl, -, -, hBB, hgn, hpde, ⟨hp0, hmod0, hq0le, -, -⟩, hlev⟩ := hH
  have hN2 : 2 ≤ H.QS * H.q * H.d :=
    H.hyp.2.1.two_le.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))
  have hcast : ((H.QS * H.q * H.d : ℕ) : ℝ) = (H.QS : ℝ) * H.q * H.d := by push_cast; ring
  have hNpos : (0 : ℝ) < (H.QS : ℝ) * H.q * H.d := by
    rw [← hcast]; exact_mod_cast (by omega : 0 < H.QS * H.q * H.d)
  have hlog := hv.log_cond_le
  obtain ⟨q1, hq, hqN, hqp, hqp', hqr, hqle⟩ := hq1 _ H.pde H.pde' hN2 H.pde_prime H.pde'_prime
    (by rw [hcast]; exact hv.2.2.2.1.1) (by rw [hcast]; exact hv.2.2.2.1.2)
  rw [hcast] at hqle
  have hqX : (q1 : ℝ) < s.X' := hx2 s _ _ hs hx.2.1 hNpos hlog hqle
  have hq0X : (q0 : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hq0le
  have hpX : (H.pde : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hv.2.2.2.1.1
  have hpX' : (H.pde' : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hv.2.2.2.1.2
  have hqg : ∀ i, q1 ≠ H.g i := fun i hi => by
    have hg := (hv.2.2.2.2.1 i).1
    rw [← hi] at hg
    have hXb := X'_le_b s
    have hk : (1 : ℝ) ≤ R.k := by
      have := R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ R.k)
    have hb1 : 1 ≤ s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)
    have h5 : s.b ≤ (R.k : ℝ) * s.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (R.k : ℝ) * s.b ≤ ((R.k : ℝ) * s.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hK : H.ccK = ⊤ := hv.2.2.2.2.2.2.1
  have hqS : q1.Coprime H.QS := by
    have h1 : q1.Coprime (H.QS * H.q * H.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hqN, Nat.gcd_one_left]
    exact (h1.coprime_mul_right_right).coprime_mul_right_right
  let H' : Host R :=
    { H with
      u0 := R.ofNat u0
      levelPrimes := insert q1 H.levelPrimes
      g_level := fun i => Finset.mem_insert_of_mem (H.g_level i)
      level_coprimeS := fun p hp => (Finset.mem_insert.1 hp).elim (fun e => e ▸ hqS) (H.level_coprimeS p)
      pde_level := ⟨Finset.mem_insert_of_mem H.pde_level.1, Finset.mem_insert_of_mem H.pde_level.2⟩
      ccK_coprime := fun p _ => by rw [hK, Ideal.absNorm_top]; exact Nat.coprime_one_left p }
  have hv' : HostVal s C.P.Cpde H' := hv
  have hmem : ∀ p ∈ H'.levelPrimes, p = q1 ∨ p = H.g 0 ∨ p = H.g 1 ∨ p = H.pde ∨ p = H.pde' ∨ p = q0 := fun p hp => by
    have hp' : p ∈ insert q1 H.levelPrimes := hp
    rw [hlev] at hp'
    simpa using hp'
  have hcond : ∀ p ∈ H'.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1 := fun p hp => by
    have h15 : ∀ z : ℕ, z % Nat.lcm 15 (H.QS * H.q * H.d) = 1 → z % (H.QS * H.q * H.d) = 1 := fun z hz => by
      rw [← Nat.mod_mod_of_dvd z (Nat.dvd_lcm_right 15 _), hz, Nat.mod_eq_of_lt hN2]
    rcases hmem p hp with h | h | h | h | h | h <;> rw [h]
    · exact ⟨hq, hqN⟩
    · exact ⟨H.g_prime 0, har.2.1 0⟩
    · exact ⟨H.g_prime 1, har.2.1 1⟩
    · exact ⟨H.pde_prime, h15 _ hpde.1⟩
    · exact ⟨H.pde'_prime, h15 _ hpde.2⟩
    · exact ⟨hp0, hmod0⟩
  obtain ⟨hcw, hc1, hc2, hc3, hc4⟩ := hx3 s R H' (fun t => a t) (fun t => b t) hs hx.2.2 hR hv'
    (fun t => ⟨(hW t t.2).1.1, (hW t t.2).2.1⟩) (Tau R) (Equiv.refl _)
  have hM0 : 0 < M := by
    rw [hM, Nat.ceil_pos]
    have hxp : 0 < s.x := by linarith [s.one_lt_alt]
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  refine ⟨H', q1, fun u => hcw (c u), ⟨0, hM0⟩, hK, hcond, hBB, fun u τ => (hc2 _ _ τ).1, fun u τ => (hc2 _ _ τ).2.1,
    fun u τ => (hc2 _ _ τ).2.2.1, fun u τ h => ((hc2 _ _ τ).2.2.2 h).1, fun u τ h => ((hc2 _ _ τ).2.2.2 h).2,
    ⟨hR, hT, hv', ⟨har.1, har.2.1, har.2.2.1, fun p hp => cls_eq_splitK_of_cond H' (hcond p hp).2⟩, ⟨hT2, hT3⟩, hdl, hgn,
      hpde, ⟨Finset.mem_insert_self _ _, hqp, hqp', hqg, hqr⟩, fun p hp => ?_, hW, ?_, hc, fun u => hc1 (c u),
      fun u => hc3 (c u), fun u => hc4 (c u)⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, Finset.subset_insert _ _, ?_, fun l => rfl, rfl⟩
  · rcases hmem p hp with h | h | h | h | h | h
    · exact Or.inr (h ▸ hqX)
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inr (h ▸ hpX)
    · exact Or.inr (h ▸ hpX')
    · exact Or.inr (h ▸ hq0X)
  · exact (Fintype.card_fin M).trans hM
  · exact R.toFrame.val_ofNat_of_lt hu

theorem chOK_of_host : SmallPrimeOne → ∀ (eps C5 c6 Cb cD ch : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 → HostGood s C.P.Cpde C5 c6 Cb H q0 → WinOK s C.GK H a b → M = ⌈3 * GamS C s R ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c → u0 < R.n → ∃ (H' : Host R) (q1 : ℕ) (hcW : Fin M → Tau R → HCParam R) (w0 : Fin M) (h1 : _) (h2 : _) (h3 : _) (h4 : _) (h5 : _) (h6 : _) (h7 : _) (h8 : _), ChOK s C cD ch (@PreCh.mk R H' h1 h2 h3 (Fin M) _ w0 hcW h4 h5 h6 h7 h8) q1 a b c ∧ H'.TT = H.TT ∧ H'.T2 = H.T2 ∧ H'.q = H.q ∧ H'.d = H.d ∧ H'.g = H.g ∧ H'.pde = H.pde ∧ H'.pde' = H.pde' ∧ H.levelPrimes ⊆ H'.levelPrimes ∧ H'.u0.val = u0 ∧ ∀ l, hPH H' l = hPH H l := by
  intro hSP eps C5 c6 Cb cD ch C he he1 hC hcD hch
  obtain ⟨x0, h⟩ := chOK_of_host_field hSP eps C5 c6 Cb cD ch C he he1 hC hcD hch
  refine ⟨x0, fun s R H q0 a b M c u0 hs hx hR hT hH hW hM hc hu => ?_⟩
  obtain ⟨H', q1, hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, -⟩ :=
    h s R H q0 a b M c u0 hs hx hR hT hH hW hM hc hu
  exact ⟨H', q1, hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩

end GlobalTheory.EX.OB
