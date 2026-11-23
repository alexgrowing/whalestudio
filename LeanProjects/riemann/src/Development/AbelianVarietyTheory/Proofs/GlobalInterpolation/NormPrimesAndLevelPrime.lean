import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesShortIntervalLowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesDyadicLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeNormOneShortInterval

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_of_pair {d M p : ℕ} (h : GlobalTheory.Mem.An.NormOne d M p) : GlobalTheory.EX.NormOne d M p := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨(A, B), h1, h2, h3⟩

open Filter Topology GlobalTheory.Mem.An.ManyNormPrimes in

private theorem many_norm_primes_mod (hTZ : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) (eps : ℝ) (he : 0 < eps) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ M d : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 0 < M → d ∣ M → Real.log M ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2 →
    ∀ Y : ℝ, 0 < Y → 8 * x ^ eps ≤ Real.log Y →
      Y ^ ((9 : ℝ) / 10) ≤ ((GlobalTheory.Mem.An.normPrimes d M Y (2 * Y)).card : ℝ) := by
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, H⟩ := GlobalTheory.T.norm_primes_short_interval_lower hTZ
  have hT : Tendsto (fun x : ℝ => x ^ (eps / 5)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have E : ∀ᶠ t : ℝ in atTop, 10000 ≤ t ∧ C₀ ≤ t ∧ Cr * Real.exp (-cr * t) ≤ 1 / 200 ∧
      40 * Real.exp (-(1 / 20) * t) ≤ c := by
    filter_upwards [eventually_ge_atTop 10000, eventually_ge_atTop C₀,
      ev_exp Cr cr (1 / 200) hcr (by norm_num), ev_exp 40 (1 / 20) c (by norm_num) hc] with t a b c d
    exact ⟨a, b, c, d⟩
  have hsq : ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ 1 / 2 * x ^ (eps / 5) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := eps / 5) 2 (by positivity)).bound (c := 1 / 2) (by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx h1
    have h0 : (0 : ℝ) ≤ x ^ (eps / 5) := Real.rpow_nonneg (by linarith) _
    rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg h0] at hx
    exact hx
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    ((hT.eventually E).and (hsq.and (eventually_gt_atTop (0 : ℝ))))
  refine ⟨x₀, fun x hx M d hd hd4 hd100 hM0 hdM hN Y hY hYx => ?_⟩
  obtain ⟨⟨t1, t2, t3, t4⟩, hl, hx0⟩ := hx₀ x hx
  have hxe : x ^ eps = (x ^ (eps / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  set t := x ^ (eps / 5) with ht
  have hMr : (d : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hM0 hdM
  have hdr : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hB1 : (1 : ℝ) < 4 * (d : ℝ) * (M : ℝ) ^ 2 := by nlinarith
  have hBt : Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ 8 * t ^ 2 := by
    have b1 : 4 * (d : ℝ) * (M : ℝ) ^ 2 ≤ 4 * (M : ℝ) ^ 3 := by nlinarith [sq_nonneg (M : ℝ)]
    have b2 := Real.log_le_log (by linarith) b1
    have hNp : (0 : ℝ) < M := by linarith
    rw [Real.log_mul (x := 4) (y := (M : ℝ) ^ 3) (by norm_num) (by positivity), Real.log_pow] at b2
    push_cast at b2
    have b3 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have b4 : t * Real.log x ^ 2 ≤ t * (1 / 2 * t) := mul_le_mul_of_nonneg_left hl (by linarith)
    nlinarith
  obtain ⟨k1, k2, k3, k4⟩ := core C₀ Cr cr c t _ Y hC₀ hCr hcr hc t1 t2 t3 t4 hB1 hBt hY
    (by rw [← hxe]; exact hYx)
  have := H d M hd hd4 hd100 (by omega) Y 1 k1 le_rfl k2 k3
  rw [show Y * (1 + 1) = 2 * Y by ring] at this
  exact k4.trans this

open Filter Topology GlobalTheory.Mem.An.ShortWindow in

private theorem exists_prime_normOne_mod (hTZ : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) (eps : ℝ) (he : 0 < eps) (cs CY : ℝ) (hcs : 0 < cs)
    (hCY : 0 < CY) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ N d g₁ g₂ m : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 0 < N → d ∣ N →
      Real.log N ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2 → 1 ≤ g₁ → 1 ≤ g₂ → Real.log g₁ ≤ CY * x ^ eps →
      Real.log g₂ ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m → ∀ W Ts : ℝ, 1 ≤ W → W ≤ x ^ (12 : ℝ) → 0 < Ts →
      cs * m * x ^ eps ≤ Real.log Ts →
      ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / W) * Ts ∧ GlobalTheory.Mem.An.NormOne d (N * (g₁ * g₂) ^ 2) T := by
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, H⟩ := GlobalTheory.T.norm_primes_short_interval_lower hTZ
  set CB : ℝ := 8 * CY + 12 with hCB
  have hCB0 : 0 < CB := by positivity
  have e1 := ev_log_le (a := 2 * eps / 5) (k := 1) (by positivity) one_pos 0 1 one_pos
  have e2 := ev_log_le (a := 1 / 3) (k := cs) (by positivity) hcs (C₀ * CB) 1 one_pos
  have e3 := ev_log_le (a := 1 / 3) (k := cr * cs / CB) (by positivity) (by positivity) (Real.log (200 * Cr)) 12 (by norm_num)
  have e4 := ev_log_le (a := 1 / 6) (k := cr * Real.sqrt cs) (by positivity) (by positivity) (Real.log (200 * Cr)) 12 (by norm_num)
  have e5 := ev_log_le (a := 1 / 3) (k := cs / 3) (by positivity) (by positivity) (7 * CB) 12 (by norm_num)
  have e6 := Real.tendsto_log_atTop.eventually_ge_atTop (100 : ℝ)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (eventually_ge_atTop (1 : ℝ))))))))
  refine ⟨x₀, fun x hx N d g₁ g₂ m hd hd4 hd100 hN0 hdN hN hg₁ hg₂ hl₁ hl₂ hm W Ts hW hWx hTs hT => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, hx1⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hW0 : 0 < W := by linarith
  set L : ℝ := x ^ eps with hL
  set u : ℝ := x ^ ((1 : ℝ) / 3) with hu
  have hL1 : 1 ≤ L := Real.one_le_rpow hx1 he.le
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by norm_num)
  have hlx : 0 ≤ Real.log x := by linarith
  have hd1 : 1 ≤ d := hd.one_lt.le
  set M : ℕ := N * (g₁ * g₂) ^ 2 with hM
  have hM1 : 1 ≤ M := Nat.succ_le_of_lt (by positivity)
  set B : ℝ := 4 * (d : ℝ) * (M : ℝ) ^ 2 with hB
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hdNR : (d : ℝ) ≤ N := by exact_mod_cast Nat.le_of_dvd hN0 hdN
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hg₁R : (1 : ℝ) ≤ g₁ := by exact_mod_cast hg₁
  have hg₂R : (1 : ℝ) ≤ g₂ := by exact_mod_cast hg₂
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hB1 : 1 < B := by
    have : (1 : ℝ) ≤ (M : ℝ) ^ 2 := one_le_pow₀ hMR
    calc (1 : ℝ) < 4 * 1 * 1 := by norm_num
      _ ≤ 4 * (d : ℝ) * (M : ℝ) ^ 2 := by gcongr
  have hB0 : 0 < B := by linarith
  have hlB0 : 0 < Real.log B := Real.log_pos hB1
  have hNL : Real.log N ≤ 3 * L := by
    have h1 : Real.log x ^ 2 ≤ (x ^ (2 * eps / 5)) ^ 2 := by
      gcongr; linarith
    have h2 : x ^ (eps / 5) * (x ^ (2 * eps / 5)) ^ 2 = L := by
      rw [hL, sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have h3 : 0 ≤ x ^ (eps / 5) := by positivity
    calc _ ≤ 3 * x ^ (eps / 5) * Real.log x ^ 2 := hN
      _ ≤ 3 * x ^ (eps / 5) * (x ^ (2 * eps / 5)) ^ 2 := by gcongr
      _ = 3 * L := by rw [mul_assoc, h2]
  have hlB : Real.log B ≤ CB * L := by
    have h1 : B ≤ 4 * (N : ℝ) ^ 3 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4 := by
      calc B = (4 * d : ℝ) * ((N : ℝ) ^ 2 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4) := by
            rw [hB, hM]; push_cast; ring
        _ ≤ (4 * N : ℝ) * ((N : ℝ) ^ 2 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4) := by gcongr
        _ = _ := by ring
    have h2 := Real.log_le_log hB0 h1
    generalize Real.log B = lB at h2 ⊢
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    have b3 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [hCB]; linarith
  have hT' : cs * u * L ≤ Real.log Ts := le_trans (by gcongr) hT
  have hT0 : 0 < Real.log Ts := lt_of_lt_of_le (by positivity) hT'
  have a1 : B ^ C₀ ≤ Ts := by
    rw [Real.rpow_def_of_pos hB0, ← Real.le_log_iff_exp_le hTs]
    calc Real.log B * C₀ ≤ CB * L * C₀ := by gcongr
      _ = (C₀ * CB) * L := by ring
      _ ≤ cs * u * L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ _ := hT'
  have a2 : 1 / W ≤ 1 := by rw [div_le_one hW0]; exact hW
  have a3 : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Ts ≤ 1 / W / 100 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have b1 : Cr * Real.exp (-(cr * Real.log Ts / Real.log B)) ≤ 1 / W / 200 := by
      refine exp_term_le hCr hx0 hW hWx (e3.trans ?_)
      rw [le_div_iff₀ hlB0]
      calc cr * cs / CB * u * Real.log B ≤ cr * cs / CB * u * (CB * L) := by gcongr
        _ = cr * (cs * u * L) := by field_simp
        _ ≤ _ := by gcongr
    have b2 : Cr * Real.exp (-(cr * Real.sqrt (Real.log Ts))) ≤ 1 / W / 200 := by
      refine exp_term_le hCr hx0 hW hWx (e4.trans ?_)
      rw [mul_assoc]
      gcongr
      apply Real.le_sqrt_of_sq_le
      have : (x ^ ((1 : ℝ) / 6)) ^ 2 = u := by
        rw [hu, sq, ← Real.rpow_add hx0]; congr 1; norm_num
      rw [mul_pow, Real.sq_sqrt hcs.le, this]
      refine le_trans ?_ hT'
      exact le_mul_of_one_le_right (by positivity) hL1
    rw [neg_mul, neg_mul, neg_div]
    linarith
  have a4 : B ^ (7 : ℝ) ≤ 1 / W * Ts ^ ((1 : ℝ) / 3) := by
    have b1 : Real.log B * 7 + Real.log x * 12 ≤ Real.log Ts * (1 / 3) := by
      have c1 : Real.log x * 12 ≤ Real.log x * 12 * L := le_mul_of_one_le_right (by positivity) hL1
      have c2 : (7 * CB + 12 * Real.log x) * L ≤ cs / 3 * u * L := by gcongr
      linarith only [c1, c2, hlB, hT']
    have b2 := Real.exp_le_exp.2 b1
    rw [Real.exp_add, ← Real.rpow_def_of_pos hB0, ← Real.rpow_def_of_pos hx0, ← Real.rpow_def_of_pos hTs] at b2
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hW0]
    refine le_trans ?_ b2
    gcongr
  have key := H d M hd hd4 hd100 hM1 Ts (1 / W) a1 a2 a3 a4
  have hpos : (0 : ℝ) < ((GlobalTheory.Mem.An.normPrimes d M Ts (Ts * (1 + 1 / W))).card : ℝ) :=
    lt_of_lt_of_le (by positivity) key
  obtain ⟨T, hTm⟩ := Finset.card_pos.1 (by exact_mod_cast hpos)
  unfold GlobalTheory.Mem.An.normPrimes at hTm
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hTm
  obtain ⟨⟨t1, t2⟩, t3, t4⟩ := hTm
  refine ⟨T, t3, Nat.lt_of_floor_lt t1, ?_, t4⟩
  rw [mul_comm]
  exact (Nat.le_floor_iff (by positivity)).1 t2

theorem normPrimes_of_TZQuad (hT : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) : NormPrimes := by
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := many_norm_primes_mod hT eps he0
  refine ⟨x0, fun s R N d hs hx hR hq => ?_⟩
  obtain ⟨hd, hd4, hd100, hN0, hdN, hN⟩ := hq
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hb : 0 < s.b := Real.exp_pos _
  have hY : 0 < ((R.k : ℝ) * s.b) ^ 8 := by positivity
  have hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hb.ne']
    have h1 : Real.log s.b = s.x ^ eps := by
      rw [← hs]; exact Real.log_exp _
    have h2 := Real.log_nonneg hk
    push_cast
    linarith
  refine (hx0 s.x hx N d hd hd4 hd100 hN0 hdN (hs ▸ hN) _ hY hlog).trans ?_
  refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
  simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  exact ⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_of_pair h4⟩

theorem levelPrime_of_quadratic (hT : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates) : LevelPrime := by
  intro eps c he0 he1 hc
  obtain ⟨x0, hx0⟩ := exists_prime_normOne_mod hT eps he0 c 9 hc (by norm_num)
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩
  obtain ⟨hd, hd4, hd100, hN0, hdN, hN⟩ := hq
  obtain ⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ :=
    hx1 s R hs (le_trans (le_max_right _ _) hx) hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : (1 : ℝ) ≤ R.f := by
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ R.f)
  have hL : s.L = s.x ^ eps := by rw [← hs]; rfl
  have hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps := by
    intro g h1 h2
    have h3 : (0 : ℝ) < g := by exact_mod_cast h1
    refine (Real.log_le_log h3 h2).trans (le_of_eq ?_)
    rw [Real.log_pow, Scale.b, Real.log_exp, hL]
    norm_num
  have hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm
  have hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le hf1 hk
  have hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ) := by
    have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.mpr hkr).trans hr
    exact (rank_mul_le hxp (by linarith) hf hk5).trans
      (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m hd hd4 hd100 hN0 hdN (hs ▸ hN)
    hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)
  exact ⟨T, hT1, hT2.le, hT3, normOne_of_pair hT4⟩

theorem normPrimes_and_levelPrime : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → NormPrimes ∧ LevelPrime :=
  fun hT => ⟨normPrimes_of_TZQuad hT, levelPrime_of_quadratic hT⟩

end GlobalTheory.EX
