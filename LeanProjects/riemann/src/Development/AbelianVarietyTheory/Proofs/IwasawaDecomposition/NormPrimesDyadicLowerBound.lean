import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesShortIntervalLowerStatement
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.ManyNormPrimes

lemma ev_log_sq (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ x ^ (eps / 5) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := eps / 5) 2 (by positivity)).bound one_pos
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx h1
  have h0 : (0 : ℝ) ≤ x ^ (eps / 5) := Real.rpow_nonneg (by linarith) _
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg h0, one_mul] at hx
  exact hx

lemma ev_exp (C c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, C * Real.exp (-c * t) ≤ δ := by
  have h1 : Tendsto (fun t : ℝ => -c * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul C
  rw [mul_zero] at h2
  exact (h2.eventually (ge_mem_nhds hδ))

lemma core (C₀ Cr cr c t B Y : ℝ) (hC₀ : 0 < C₀) (hCr : 0 < Cr) (hcr : 0 < cr) (hc : 0 < c)
    (ht : 10000 ≤ t) (htC : C₀ ≤ t) (h1 : Cr * Real.exp (-cr * t) ≤ 1 / 200)
    (h2 : 40 * Real.exp (-(1 / 20) * t) ≤ c) (hB : 1 < B) (hBt : Real.log B ≤ 8 * t ^ 2)
    (hY : 0 < Y) (hYt : 8 * t ^ 5 ≤ Real.log Y) :
    B ^ C₀ ≤ Y ∧ Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Y ≤ 1 / 100 ∧ B ^ (7 : ℝ) ≤ 1 * Y ^ ((1 : ℝ) / 3) ∧
      Y ^ ((9 : ℝ) / 10) ≤ c * 1 * B ^ (-6 : ℝ) * Y / Real.log Y := by
  have hB0 : 0 < B := by linarith
  have hlB : 0 < Real.log B := Real.log_pos hB
  set L := Real.log Y with hL
  set b := Real.log B with hb
  have ht1 : 1 ≤ t := by linarith
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have ht3 : 10000 * t ≤ t ^ 3 := by nlinarith
  have ht5 : t ^ 5 = t ^ 3 * t ^ 2 := by ring
  have hbL : 10000 * t * b ≤ L := by
    have : 10000 * t * b ≤ t ^ 3 * (8 * t ^ 2) :=
      mul_le_mul ht3 hBt hlB.le (by positivity)
    nlinarith
  have htb : b ≤ t * b := by nlinarith
  have ht2L : t ^ 2 ≤ L := by
    have : t ^ 2 ≤ t ^ 5 := pow_le_pow_right₀ ht1 (by norm_num)
    nlinarith [sq_nonneg t]
  have hL0 : 0 < L := by linarith
  have hYe : Y = Real.exp L := (Real.exp_log hY).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hB0, hYe]
    apply Real.exp_le_exp.2
    nlinarith
  · unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have e1 : -cr * L / b ≤ -cr * t := by
      rw [div_le_iff₀ hlB]
      have : t * b ≤ L := by nlinarith
      nlinarith
    have e2 : -cr * √L ≤ -cr * t := by
      have : t ≤ √L := Real.le_sqrt_of_sq_le ht2L
      nlinarith
    have f1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 e1) hCr.le
    have f2 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 e2) hCr.le
    linarith
  · rw [Real.rpow_def_of_pos hB0, Real.rpow_def_of_pos hY, one_mul]
    apply Real.exp_le_exp.2
    nlinarith
  · rw [Real.rpow_def_of_pos hB0, Real.rpow_def_of_pos hY, mul_one, le_div_iff₀ hL0, ← hL, ← hb]
    have g1 : L ≤ 40 * Real.exp (L / 40) := by
      have := Real.add_one_le_exp (L / 40)
      linarith
    have g2 : 40 * Real.exp (-(1 / 20) * L) ≤ c := by
      have : Real.exp (-(1 / 20) * L) ≤ Real.exp (-(1 / 20) * t) := Real.exp_le_exp.2 (by linarith)
      linarith
    calc Real.exp (L * (9 / 10)) * L ≤ Real.exp (L * (9 / 10)) * (40 * Real.exp (L / 40)) := by gcongr
      _ = 40 * Real.exp (L * (9 / 10) + L / 40) := by rw [Real.exp_add]; ring
      _ ≤ 40 * Real.exp (-(1 / 20) * L + b * (-6) + L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
          linarith
      _ = 40 * Real.exp (-(1 / 20) * L) * Real.exp (b * (-6)) * Real.exp L := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ c * Real.exp (b * (-6)) * Real.exp L := by gcongr
      _ = c * Real.exp (b * (-6)) * Y := by rw [← hYe]

theorem many_norm_primes : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n q d : ℕ, 1 ≤ n → Rowq x eps n q d → ∀ Y : ℝ, 0 < Y → 8 * x ^ eps ≤ Real.log Y → Y ^ ((9 : ℝ) / 10) ≤ ((normPrimes d (4 * n * q * d) Y (2 * Y)).card : ℝ) := by
  intro hTZ eps he _
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, H⟩ := GlobalTheory.T.norm_primes_short_interval_lower hTZ
  have hT : Tendsto (fun x : ℝ => x ^ (eps / 5)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have E : ∀ᶠ t : ℝ in atTop, 10000 ≤ t ∧ C₀ ≤ t ∧ Cr * Real.exp (-cr * t) ≤ 1 / 200 ∧
      40 * Real.exp (-(1 / 20) * t) ≤ c := by
    filter_upwards [eventually_ge_atTop 10000, eventually_ge_atTop C₀,
      ev_exp Cr cr (1 / 200) hcr (by norm_num), ev_exp 40 (1 / 20) c (by norm_num) hc] with t a b c d
    exact ⟨a, b, c, d⟩
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    ((hT.eventually E).and ((ev_log_sq eps he).and (hlog.and (eventually_gt_atTop (0 : ℝ)))))
  refine ⟨x₀, fun x hx n q d hn hR Y hY hYx => ?_⟩
  obtain ⟨⟨t1, t2, t3, t4⟩, hl, hl1, hx0⟩ := hx₀ x hx
  obtain ⟨hq, -, -, -, hd, hd16, hdl, -, -, -, hN⟩ := hR
  have hxe : x ^ eps = (x ^ (eps / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  unfold GlobalTheoryTheory.X2 at hdl
  set t := x ^ (eps / 5) with ht
  have hd100 : 100 ≤ d := by
    have a1 : t ≤ t * Real.log x ^ 2 :=
      le_mul_of_one_le_right (by linarith) (one_le_pow₀ hl1)
    have a2 := Real.add_one_le_exp (t * Real.log x ^ 2)
    have a3 : (100 : ℝ) ≤ √(Real.exp (t * Real.log x ^ 2)) :=
      Real.le_sqrt_of_sq_le (by linarith)
    have : (100 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hM : 4 * d ≤ 4 * n * q * d := by
    have : 1 ≤ n * q := Nat.mul_pos hn hq1
    nlinarith
  set M : ℕ := 4 * n * q * d with hMdef
  have hMc : (M : ℝ) = 4 * n * q * d := by rw [hMdef]; push_cast; ring
  rw [← hMc] at hN
  have hMr : 4 * (d : ℝ) ≤ M := by exact_mod_cast hM
  have hdr : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hB1 : (1 : ℝ) < 4 * (d : ℝ) * (M : ℝ) ^ 2 := by nlinarith
  have hBt : Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ 8 * t ^ 2 := by
    have b1 : 4 * (d : ℝ) * (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 := by nlinarith [sq_nonneg (M : ℝ)]
    have b2 := Real.log_le_log (by linarith) b1
    rw [Real.log_pow] at b2
    push_cast at b2
    nlinarith
  obtain ⟨k1, k2, k3, k4⟩ := core C₀ Cr cr c t _ Y hC₀ hCr hcr hc t1 t2 t3 t4 hB1 hBt hY
    (by rw [← hxe]; exact hYx)
  have := H d M hd (by omega) hd100 (by omega) Y 1 k1 le_rfl k2 k3
  rw [show Y * (1 + 1) = 2 * Y by ring] at this
  exact k4.trans this

end GlobalTheory.Mem.An.ManyNormPrimes
