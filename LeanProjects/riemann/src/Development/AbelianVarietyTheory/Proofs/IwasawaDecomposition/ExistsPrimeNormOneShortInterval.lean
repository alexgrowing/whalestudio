import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesShortIntervalLowerStatement

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.ShortWindow

theorem ev_log_le {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (A D : ℝ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, A + D * Real.log x ≤ k * x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := k / 2 / D) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (A / (k / 2))
  filter_upwards [h1, h2, eventually_ge_atTop (0 : ℝ)] with x h1 h2 hx
  have hp : 0 ≤ x ^ a := Real.rpow_nonneg hx a
  rw [Real.norm_of_nonneg hp] at h1
  have h3 : Real.log x ≤ k / 2 / D * x ^ a := (le_abs_self _).trans h1
  have h4 : D * Real.log x ≤ k / 2 * x ^ a := by
    calc D * Real.log x ≤ D * (k / 2 / D * x ^ a) := by gcongr
      _ = k / 2 * x ^ a := by field_simp
  have h5 : A ≤ k / 2 * x ^ a := by
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  linarith

theorem exp_term_le {C x W y : ℝ} (hC : 0 < C) (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x ^ (12 : ℝ))
    (hy : Real.log (200 * C) + 12 * Real.log x ≤ y) : C * Real.exp (-y) ≤ 1 / W / 200 := by
  have h1 : 200 * C * W ≤ Real.exp y := by
    calc 200 * C * W ≤ 200 * C * x ^ (12 : ℝ) := by gcongr
      _ = Real.exp (Real.log (200 * C) + 12 * Real.log x) := by
        rw [Real.exp_add, Real.exp_log (by positivity), Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
      _ ≤ _ := Real.exp_le_exp.2 hy
  have hW0 : 0 < W := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith

theorem exists_prime_normOne : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ cs CY : ℝ, 0 < cs → 0 < CY → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n q d g₁ g₂ m : ℕ, 1 ≤ n → Rowq x eps n q d → 1 ≤ g₁ → 1 ≤ g₂ → Real.log g₁ ≤ CY * x ^ eps → Real.log g₂ ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m → ∀ W Ts : ℝ, 1 ≤ W → W ≤ x ^ (12 : ℝ) → 0 < Ts → cs * m * x ^ eps ≤ Real.log Ts → ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / W) * Ts ∧ NormOne d (4 * n * q * d * (g₁ * g₂) ^ 2) T := by
  intro hTZ eps he _ cs CY hcs hCY
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, H⟩ := GlobalTheory.T.norm_primes_short_interval_lower hTZ
  set CB : ℝ := 8 * CY + 6 with hCB
  have hCB0 : 0 < CB := by positivity
  have e1 := ev_log_le (a := 2 * eps / 5) (k := 1) (by positivity) one_pos 0 1 one_pos
  have e2 := ev_log_le (a := 1 / 3) (k := cs) (by positivity) hcs (C₀ * CB) 1 one_pos
  have e3 := ev_log_le (a := 1 / 3) (k := cr * cs / CB) (by positivity) (by positivity) (Real.log (200 * Cr)) 12 (by norm_num)
  have e4 := ev_log_le (a := 1 / 6) (k := cr * Real.sqrt cs) (by positivity) (by positivity) (Real.log (200 * Cr)) 12 (by norm_num)
  have e5 := ev_log_le (a := 1 / 3) (k := cs / 3) (by positivity) (by positivity) (7 * CB) 12 (by norm_num)
  have e6 := Real.tendsto_log_atTop.eventually_ge_atTop (100 : ℝ)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (eventually_ge_atTop (1 : ℝ))))))))
  refine ⟨x₀, fun x hx n q d g₁ g₂ m hn hR hg₁ hg₂ hl₁ hl₂ hm W Ts hW hWx hTs hT => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, hx1⟩ := hx₀ x hx
  obtain ⟨hq, -, -, -, hd, hd16, hdl, -, -, -, hN⟩ := hR
  have hx0 : 0 < x := by linarith
  have hW0 : 0 < W := by linarith
  set L : ℝ := x ^ eps with hL
  set u : ℝ := x ^ ((1 : ℝ) / 3) with hu
  have hL1 : 1 ≤ L := Real.one_le_rpow hx1 he.le
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by norm_num)
  have hlx : 0 ≤ Real.log x := by linarith
  have hd100 : 100 ≤ d := by
    have h1 : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hx1 (by positivity)
    have h2 : (10000 : ℝ) ≤ x ^ (eps / 5) * Real.log x ^ 2 := by
      calc (10000 : ℝ) = 1 * 100 ^ 2 := by norm_num
        _ ≤ _ := by gcongr
    have h3 : (100 : ℝ) ^ 2 ≤ GlobalTheoryTheory.X2 x eps := by
      have := Real.add_one_le_exp (x ^ (eps / 5) * Real.log x ^ 2)
      unfold GlobalTheoryTheory.X2
      linarith
    have h4 : (100 : ℝ) ≤ Real.sqrt (GlobalTheoryTheory.X2 x eps) := Real.le_sqrt_of_sq_le h3
    have h5 : (100 : ℝ) ≤ d := by linarith
    exact_mod_cast h5
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hd1 : 1 ≤ d := hd.one_lt.le
  set M : ℕ := 4 * n * q * d * (g₁ * g₂) ^ 2 with hM
  have hM1 : 1 ≤ M := Nat.succ_le_of_lt (by positivity)
  set B : ℝ := 4 * (d : ℝ) * (M : ℝ) ^ 2 with hB
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
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
  have hNL : Real.log (4 * n * q * d) ≤ 2 * L := by
    have h1 : Real.log x ^ 2 ≤ (x ^ (2 * eps / 5)) ^ 2 := by
      gcongr; linarith
    have h2 : x ^ (eps / 5) * (x ^ (2 * eps / 5)) ^ 2 = L := by
      rw [hL, sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have h3 : 0 ≤ x ^ (eps / 5) := by positivity
    calc _ ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 := hN
      _ ≤ 2 * x ^ (eps / 5) * (x ^ (2 * eps / 5)) ^ 2 := by gcongr
      _ = 2 * L := by rw [mul_assoc, h2]
  have hlB : Real.log B ≤ CB * L := by
    have h1 : B ≤ (4 * n * q * d : ℝ) ^ 3 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4 := by
      have h0 : (4 * d : ℝ) ≤ 4 * n * q * d := by
        calc (4 * d : ℝ) = 4 * 1 * 1 * d := by ring
          _ ≤ _ := by gcongr
      calc B = (4 * d : ℝ) * ((4 * n * q * d : ℝ) ^ 2 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4) := by
            rw [hB, hM]; push_cast; ring
        _ ≤ (4 * n * q * d : ℝ) * ((4 * n * q * d : ℝ) ^ 2 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4) := by gcongr
        _ = _ := by ring
    have h2 := Real.log_le_log hB0 h1
    generalize Real.log B = lB at h2 ⊢
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at h2
    push_cast at h2
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
  have key := H d M hd (by omega) hd100 hM1 Ts (1 / W) a1 a2 a3 a4
  have hpos : (0 : ℝ) < ((normPrimes d M Ts (Ts * (1 + 1 / W))).card : ℝ) :=
    lt_of_lt_of_le (by positivity) key
  obtain ⟨T, hTm⟩ := Finset.card_pos.1 (by exact_mod_cast hpos)
  unfold normPrimes at hTm
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hTm
  obtain ⟨⟨t1, t2⟩, t3, t4⟩ := hTm
  refine ⟨T, t3, Nat.lt_of_floor_lt t1, ?_, t4⟩
  rw [mul_comm]
  exact (Nat.le_floor_iff (by positivity)).1 t2

end GlobalTheory.Mem.An.ShortWindow
