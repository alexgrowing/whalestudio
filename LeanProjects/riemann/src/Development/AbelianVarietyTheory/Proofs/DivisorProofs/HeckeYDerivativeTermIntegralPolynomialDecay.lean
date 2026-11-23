import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntZEqFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeTermDecayFourierIntegralLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHeckeTermDecayIntegrandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeckeTermDecayIntegrandStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.TermDecay

theorem intZ_ibp (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) (a : ℤ) (b m : ℕ) (hab : 2 ≤ a + 2 * b) {y : ℝ}
    (hy : y ≠ 0) :
    2 * (Real.pi : ℂ) * I * ν * intZ σ ν a b m y =
      -(a : ℂ) * intZ σ ν (a + 1) b m y
        + 2 * (-σ - (b : ℂ)) * (intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y) := by
  have i0 := GlobalTheory.T.integrable_heckeTermDecayIntegrand σ hσ a b m hab y hy
  have i1 := GlobalTheory.T.integrable_heckeTermDecayIntegrand σ hσ (a + 1) b m (by omega) y hy
  have i2 := GlobalTheory.T.integrable_heckeTermDecayIntegrand σ hσ (a - 1) (b + 1) m (by push_cast; omega) y hy
  have i3 := GlobalTheory.T.integrable_heckeTermDecayIntegrand σ hσ a (b + 1) (m + 1) (by push_cast; omega) y hy
  have hd : deriv (qZ σ a b m y) = fun t => -(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t) := by
    funext t; exact (GlobalTheory.T.hasDerivAt_heckeTermDecayIntegrand σ a b m y hy t).deriv
  have hdiff : Differentiable ℝ (qZ σ a b m y) := fun t => (GlobalTheory.T.hasDerivAt_heckeTermDecayIntegrand σ a b m y hy t).differentiableAt
  have hi : MeasureTheory.Integrable (deriv (qZ σ a b m y)) := by
    rw [hd]; exact (i1.const_mul _).add ((i2.sub (i3.const_mul _)).const_mul _)
  have key := congrFun (Real.fourier_deriv i0 hdiff hi) ν
  rw [← intZ_eq_fourier, smul_eq_mul] at key
  rw [← key, hd, Real.fourier_real_eq_integral_exp_smul]
  unfold intZ
  set E : ℝ → ℂ := fun t => Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) with hE
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hEn : ∀ t, ‖E t‖ = 1 := by
    intro t; rw [hE, Complex.norm_exp]; simp
  have e : ∀ (f : ℝ → ℂ), MeasureTheory.Integrable f → MeasureTheory.Integrable (fun t : ℝ => f t * E t) := by
    intro f hf
    refine hf.norm.mono' (hf.aestronglyMeasurable.mul hEc.aestronglyMeasurable) (MeasureTheory.ae_of_all _ fun t => ?_)
    rw [norm_mul, hEn, mul_one]
  have hpt : ∀ t : ℝ, Complex.exp (((-2 * Real.pi * t * ν : ℝ) : ℂ) * I) •
      (-(a : ℂ) * qZ σ (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t))
      = -(a : ℂ) * (qZ σ (a + 1) b m y t * E t) + 2 * (-σ - (b : ℂ)) *
        (qZ σ (a - 1) (b + 1) m y t * E t - I * (qZ σ a (b + 1) (m + 1) y t * E t)) := by
    intro t
    rw [smul_eq_mul, hE]
    have : (((-2 * Real.pi * t * ν : ℝ) : ℂ) * I) = -(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)) := by push_cast; ring
    rw [this]; ring
  simp_rw [hpt]
  have j1 : MeasureTheory.Integrable (fun v => -(a : ℂ) * (qZ σ (a + 1) b m y v * E v)) := (e _ i1).const_mul _
  have j2 : MeasureTheory.Integrable (fun v => qZ σ (a - 1) (b + 1) m y v * E v) := e _ i2
  have j3 : MeasureTheory.Integrable (fun v => I * (qZ σ a (b + 1) (m + 1) y v * E v)) := (e _ i3).const_mul _
  have j23 : MeasureTheory.Integrable (fun v => 2 * (-σ - (b : ℂ)) *
      (qZ σ (a - 1) (b + 1) m y v * E v - I * (qZ σ a (b + 1) (m + 1) y v * E v))) := (j2.sub j3).const_mul _
  rw [MeasureTheory.integral_add j1 j23, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub j2 j3, MeasureTheory.integral_const_mul]

end GlobalTheory.HeckeTwo.TermDecay

namespace GlobalTheory.HeckeTwo.TermDecay

theorem le_div_one_add_pow_succ_of_mul_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) (A B Y : ℝ) (hY : 0 ≤ Y) (hA : 0 ≤ A) (hB : 0 ≤ B) (q : ℝ)
    (h0 : q ≤ A * Y) (h1 : x * q ≤ B * Y / (1 + x) ^ N) :
    q ≤ (2 ^ (N + 1) * A + 2 * B) * Y / (1 + x) ^ (N + 1) := by
  have hp : 0 < (1 + x) ^ (N + 1) := by positivity
  rw [le_div_iff₀ hp]
  rcases le_or_gt x 1 with h | h
  · have h2 : (1 + x) ^ (N + 1) ≤ 2 ^ (N + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
    rcases le_or_gt q 0 with hq | hq
    · have : 0 ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by positivity
      nlinarith [hp]
    · calc q * (1 + x) ^ (N + 1) ≤ A * Y * 2 ^ (N + 1) := mul_le_mul h0 h2 hp.le (by positivity)
        _ ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by nlinarith [mul_nonneg hB hY]
  · have hpN : 0 < (1 + x) ^ N := by positivity
    have h1' : x * q * (1 + x) ^ N ≤ B * Y := by rwa [le_div_iff₀ hpN] at h1
    have hx2 : 1 + x ≤ 2 * x := by linarith
    rcases le_or_gt q 0 with hq | hq
    · have : 0 ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by positivity
      nlinarith [hp]
    · calc q * (1 + x) ^ (N + 1) = q * (1 + x) ^ N * (1 + x) := by ring
        _ ≤ q * (1 + x) ^ N * (2 * x) := by gcongr
        _ = 2 * (x * q * (1 + x) ^ N) := by ring
        _ ≤ 2 * (B * Y) := by linarith
        _ ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (N + 1)) hA) hY]

theorem intZ_decay (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ halfPlane) (N : ℕ) :
    ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∃ C : ℝ, ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖intZ σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  induction N with
  | zero =>
    intro a b m hab
    obtain ⟨C, hC⟩ := GlobalTheory.T.norm_heckeTermDecayFourierIntegral_le K hK hKH a b m hab
    exact ⟨C, fun σ hσ ν y _ hy => by simpa using hC σ hσ ν y hy⟩
  | succ N ih =>
    intro a b m hab
    obtain ⟨C0, hC0⟩ := GlobalTheory.T.norm_heckeTermDecayFourierIntegral_le K hK hKH a b m hab
    obtain ⟨C1, hC1⟩ := ih (a + 1) b m (by omega)
    obtain ⟨C2, hC2⟩ := ih (a - 1) (b + 1) m (by push_cast; omega)
    obtain ⟨C3, hC3⟩ := ih a (b + 1) (m + 1) (by push_cast; omega)
    set B : ℝ := (|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) / (2 * Real.pi) with hB
    refine ⟨2 ^ (N + 1) * |C0| + 2 * B, fun σ hσ ν y hν hy => ?_⟩
    set E : ℝ := (m : ℝ) + 1 - a - 2 * b - 2 * σ.re with hE
    have hyp : 0 < |y| := abs_pos.2 hy
    have hnp : 0 < |ν| := abs_pos.2 hν
    have hx : |ν * y| = |ν| * |y| := abs_mul ν y
    have hpN : 0 < (1 + |ν * y|) ^ N := by positivity
    have hB0 : 0 ≤ B := by rw [hB]; have := Real.pi_pos; positivity
    refine le_trans ?_ (le_of_eq (by ring : (2 ^ (N + 1) * |C0| + 2 * B) * |y| ^ E / (1 + |ν * y|) ^ (N + 1) =
      (2 ^ (N + 1) * |C0| + 2 * B) * |y| ^ E / (1 + |ν * y|) ^ (N + 1)))
    apply le_div_one_add_pow_succ_of_mul_le |ν * y| (abs_nonneg _) N |C0| B (|y| ^ E) (by positivity) (abs_nonneg _) hB0
    · exact (hC0 σ hσ ν y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    ·
      have hibp := intZ_ibp σ (hKH hσ) ν a b m hab hy
      have e1 := hC1 σ hσ ν y hν hy
      have e2 := hC2 σ hσ ν y hν hy
      have e3 := hC3 σ hσ ν y hν hy
      have hE1 : ((m : ℝ) + 1 - ((a + 1 : ℤ) : ℝ) - 2 * b - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      have hE2 : ((m : ℝ) + 1 - ((a - 1 : ℤ) : ℝ) - 2 * ((b + 1 : ℕ) : ℝ) - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      have hE3 : (((m + 1 : ℕ) : ℝ) + 1 - (a : ℝ) - 2 * ((b + 1 : ℕ) : ℝ) - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      rw [hE1] at e1; rw [hE2] at e2; rw [hE3] at e3
      set X : ℝ := |y| ^ (E - 1) / (1 + |ν * y|) ^ N with hX
      have hX0 : 0 ≤ X := by positivity
      have hσb : ‖-σ - (b : ℂ)‖ ≤ |R| + b := by
        calc ‖-σ - (b : ℂ)‖ ≤ ‖σ‖ + ‖(b : ℂ)‖ := by rw [← norm_neg σ]; exact norm_sub_le _ _
          _ ≤ |R| + b := by rw [Complex.norm_natCast]; gcongr; exact (hR σ hσ).trans (le_abs_self R)
      have key : 2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖ ≤ (|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) * X := by
        have hn : ‖2 * (Real.pi : ℂ) * I * ν * intZ σ ν a b m y‖ = 2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖ := by
          simp [norm_mul, Complex.norm_real, abs_of_pos Real.pi_pos]
        rw [← hn, hibp]
        have f1 : ‖intZ σ ν (a + 1) b m y‖ ≤ |C1| * X := by
          rw [hX, ← mul_div_assoc]; exact e1.trans (by gcongr; exact le_abs_self _)
        have f2 : ‖intZ σ ν (a - 1) (b + 1) m y‖ ≤ |C2| * X := by
          rw [hX, ← mul_div_assoc]; exact e2.trans (by gcongr; exact le_abs_self _)
        have f3 : ‖intZ σ ν a (b + 1) (m + 1) y‖ ≤ |C3| * X := by
          rw [hX, ← mul_div_assoc]; exact e3.trans (by gcongr; exact le_abs_self _)
        calc _ ≤ ‖-(a : ℂ) * intZ σ ν (a + 1) b m y‖ + ‖2 * (-σ - (b : ℂ)) *
              (intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y)‖ := norm_add_le _ _
          _ ≤ |(a : ℝ)| * (|C1| * X) + 2 * (|R| + b) * (|C2| * X + |C3| * X) := by
            rw [norm_mul, norm_mul, norm_neg, norm_mul]
            have ha : ‖(a : ℂ)‖ = |(a : ℝ)| := by rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
            rw [ha]
            have hs : ‖intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y‖ ≤ |C2| * X + |C3| * X := by
              refine (norm_sub_le _ _).trans (add_le_add f2 ?_)
              rw [norm_mul, Complex.norm_I, one_mul]; exact f3
            gcongr
            · simp
          _ = _ := by ring

      have hyE : |y| ^ (E - 1) = |y| ^ E / |y| := by rw [Real.rpow_sub_one hyp.ne']
      have h2p : 0 < 2 * Real.pi * |ν| := by have := Real.pi_pos; positivity
      rw [hx]
      have : |ν| * |y| * ‖intZ σ ν a b m y‖ = |y| / (2 * Real.pi) * (2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖) := by
        field_simp
      rw [this]
      calc |y| / (2 * Real.pi) * (2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖)
          ≤ |y| / (2 * Real.pi) * ((|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) * X) := by gcongr
        _ = B * |y| ^ E / (1 + |ν| * |y|) ^ N := by
          rw [hB, hX, hyE, ← hx]; field_simp

end GlobalTheory.HeckeTwo.TermDecay

open GlobalTheory.HeckeTwo.TermDecay in

theorem GlobalTheory.HeckeTwo.TermDecay.intT_bound : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  intro K hK hKH a b m hab N
  obtain ⟨C, hC⟩ := intZ_decay K hK hKH N (a : ℤ) b m (by exact_mod_cast hab)
  refine ⟨C, fun σ hσ ν y hν hy => ?_⟩
  rw [intT_eq_intZ]
  have := hC σ hσ ν y hν hy
  simpa using this
