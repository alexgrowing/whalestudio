import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntZEqFourier
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

theorem norm_qZ_mul_exp (σ : ℂ) (ν : ℝ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    ‖qZ σ a b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))‖ =
      (t ^ 2 + y ^ 2) ^ (-((a : ℝ) / 2 + b + σ.re)) * |y| ^ m := by
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold qZ
  rw [norm_mul, norm_mul, norm_mul, norm_zpow, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hQ.le,
    ← Real.rpow_add hQ]
  congr 2
  simp
  ring

theorem integral_rpow_sq_add_sq (e : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ∫ t : ℝ, (t ^ 2 + y ^ 2) ^ (-e) = |y| ^ (1 - 2 * e) * ∫ s : ℝ, (1 + s ^ 2) ^ (-e) := by
  have hc : 0 < |y| := abs_pos.2 hy
  have hpt : ∀ t : ℝ, (t ^ 2 + y ^ 2) ^ (-e) = |y| ^ (-2 * e) * (1 + (t / |y|) ^ 2) ^ (-e) := by
    intro t
    have h1 : t ^ 2 + y ^ 2 = |y| ^ 2 * (1 + (t / |y|) ^ 2) := by
      field_simp
      rw [sq_abs]
      ring
    rw [h1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_div (fun s : ℝ => (1 + s ^ 2) ^ (-e)) |y|, abs_abs, smul_eq_mul,
    ← mul_assoc, show 1 - 2 * e = -2 * e + 1 by ring, Real.rpow_add_one hc.ne']

theorem norm_intZ_le : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, y ≠ 0 →
      ‖intZ σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) := by
  intro K hK hKH a b m hab
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun σ hσ => by simp at hσ⟩
  obtain ⟨σ₀, hσ₀K, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  have hσ₀ : -1 / 2 < σ₀.re := hKH hσ₀K
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  set e₀ : ℝ := (a : ℝ) / 2 + b + σ₀.re with he₀
  have he₀1 : 1 / 2 < e₀ := by rw [he₀]; linarith
  have hg₀ : MeasureTheory.Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-e₀)) := by
    have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := MeasureTheory.volume) (r := 2 * e₀) (by simp; linarith)
    refine this.congr (MeasureTheory.ae_of_all _ fun s => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  refine ⟨∫ s : ℝ, (1 + s ^ 2) ^ (-e₀), ?_⟩
  intro σ hσ ν y hy
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hee : e₀ ≤ e := by
    have := hmin hσ
    simp only [Set.mem_setOf_eq] at this
    rw [he, he₀]; linarith
  have hc : 0 < |y| := abs_pos.2 hy
  have hmono : (∫ s : ℝ, (1 + s ^ 2) ^ (-e)) ≤ ∫ s : ℝ, (1 + s ^ 2) ^ (-e₀) :=
    MeasureTheory.integral_mono_of_nonneg (MeasureTheory.ae_of_all _ fun s => by positivity) hg₀
      (MeasureTheory.ae_of_all _ fun s =>
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg s]) (by linarith))
  calc ‖intZ σ ν a b m y‖
      ≤ ∫ t : ℝ, ‖qZ σ a b m y t * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m := by
        simp_rw [norm_qZ_mul_exp σ ν a b m hy]
        rw [he]
    _ = (|y| ^ (1 - 2 * e) * ∫ s : ℝ, (1 + s ^ 2) ^ (-e)) * |y| ^ m := by
        rw [MeasureTheory.integral_mul_const, integral_rpow_sq_add_sq e hy]
    _ ≤ (|y| ^ (1 - 2 * e) * ∫ s : ℝ, (1 + s ^ 2) ^ (-e₀)) * |y| ^ m := by
        gcongr
    _ = (∫ s : ℝ, (1 + s ^ 2) ^ (-e₀)) * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) := by
        rw [← Real.rpow_natCast, mul_comm (|y| ^ (1 - 2 * e)), mul_assoc, ← Real.rpow_add hc, he]
        congr 2
        ring

end GlobalTheory.HeckeTwo.TermDecay
