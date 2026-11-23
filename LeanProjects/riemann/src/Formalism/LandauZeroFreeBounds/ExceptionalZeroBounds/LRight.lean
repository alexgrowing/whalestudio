import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma norm_term_twist_moebius_le {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    ‖term (↗χ * ↗μ) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  apply LSeries.norm_term_le
  simp only [Pi.mul_apply, Pi.one_apply, norm_one, norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ (n : ZMod q)
  have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact mul_le_one₀ h1 (norm_nonneg _) h2

open Formalism.ZF.MoebiusInverseZetaBounds in
theorem inverseBound : LInvBound := by
  intro q _ χ s hs
  have hσ1 : 0 < s.re - 1 := by linarith
  have hshift : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) ≤ s.re / (s.re - 1) := by
    apply Real.tsum_le_of_sum_range_le
    · intro n
      positivity
    · intro m
      rcases m with _ | k
      · simp only [Finset.range_zero, Finset.sum_empty]
        positivity
      · rw [Finset.sum_range_succ']
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hanti : AntitoneOn (fun x : ℝ => x ^ (-s.re)) (Set.Icc (1 : ℝ) (1 + k)) := by
          intro x hx y _ hxy
          exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
        have hsum := hanti.sum_le_integral
        have hint : ∫ x in (1 : ℝ)..(1 + k), x ^ (-s.re) =
            ((1 + k : ℝ) ^ (-s.re + 1) - 1 ^ (-s.re + 1)) / (-s.re + 1) := by
          apply integral_rpow
          refine Or.inr ⟨by linarith, ?_⟩
          rw [Set.uIcc_of_le (by linarith)]
          intro h
          linarith [h.1]
        have hpos : 0 ≤ (1 + k : ℝ) ^ (-s.re + 1) := by positivity
        have hb : ((1 + k : ℝ) ^ (-s.re + 1) - 1 ^ (-s.re + 1)) / (-s.re + 1) ≤ 1 / (s.re - 1) := by
          rw [Real.one_rpow, show -s.re + 1 = -(s.re - 1) by ring, div_neg, ← neg_div]
          have hpos' : 0 ≤ (1 + k : ℝ) ^ (-(s.re - 1)) := by positivity
          gcongr
          linarith
        have e : ∑ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + 1) ^ (-(s.re - 1) - 1) =
            ∑ i ∈ Finset.range k, (fun x : ℝ => x ^ (-s.re)) (1 + ((i + 1 : ℕ) : ℝ)) :=
          Finset.sum_congr rfl fun i _ => by
            show (((i + 1 : ℕ) : ℝ) + 1) ^ (-(s.re - 1) - 1) = (1 + ((i + 1 : ℕ) : ℝ)) ^ (-s.re)
            congr 1 <;> ring
        rw [e]
        have e2 : s.re / (s.re - 1) = 1 / (s.re - 1) + 1 := by
          field_simp
          ring
        simp only [Nat.cast_zero, zero_add, Real.one_rpow]
        rw [hint] at hsum
        linarith
  have hp : -(s.re - 1) - 1 < -1 := by linarith
  have hfun : (fun n : ℕ => ‖term (1 : ℕ → ℂ) s (n + 1)‖) = fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) :=
    funext (norm_term_one_succ s)
  have hS1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ := by
    rw [← summable_nat_add_iff 1, hfun]
    exact summable_shift hp
  have hT1 : ∑' n, ‖term (1 : ℕ → ℂ) s n‖ ≤ s.re / (s.re - 1) := by
    rw [hS1.tsum_eq_zero_add, LSeries.term_zero, norm_zero, zero_add, hfun]
    exact hshift
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hinv : ‖LSeries ↗χ s‖⁻¹ = ‖LSeries (↗χ * ↗μ) s‖ := by
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hmul]
  rw [hinv]
  have hS2 : Summable fun n => ‖term (↗χ * ↗μ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_term_twist_moebius_le χ s n) hS1
  calc ‖LSeries (↗χ * ↗μ) s‖ = ‖∑' n, term (↗χ * ↗μ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗μ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ :=
      Summable.tsum_le_tsum (fun n => norm_term_twist_moebius_le χ s n) hS2 hS1
    _ ≤ s.re / (s.re - 1) := hT1

lemma negLD_eq_LSeries_mul_vonMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    negLD χ s = L (↗χ * ↗Λ) s := by
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries ↗χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [negLD, hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, neg_div]

lemma norm_LSeries_twist_vonMangoldt_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖L (↗χ * ↗Λ) s‖ ≤ Formalism.ZF.lamF s.re := by
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  have hSΛ : Summable fun n => ‖term ↗Λ (s.re : ℂ) n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  have hle : ∀ n, ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ (s.re : ℂ) n‖ := by
    intro n
    calc ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ s n‖ := by
          apply LSeries.norm_term_le
          simp only [Pi.mul_apply, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
      _ = ‖term ↗Λ (s.re : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re]
  have hS2 : Summable fun n => ‖term (↗χ * ↗Λ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hSΛ
  calc ‖L (↗χ * ↗Λ) s‖ = ‖∑' n, term (↗χ * ↗Λ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term ↗Λ (s.re : ℂ) n‖ := Summable.tsum_le_tsum hle hS2 hSΛ
    _ = Formalism.ZF.lamF s.re := rfl

theorem l_log_deriv_right : LLogDerivRight := by
  obtain ⟨C, hC0, hC⟩ := Formalism.ZF.logDerivBoundRightHalfPlane
  refine ⟨C, hC0, ?_⟩
  intro q _ χ s hs
  rw [negLD_eq_LSeries_mul_vonMangoldt χ hs]
  refine le_trans (norm_LSeries_twist_vonMangoldt_le χ hs) ?_
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  rw [Formalism.ZF.lamF_eq_norm hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre,
    neg_div, norm_neg]
  have h := hC (s.re : ℂ) hre
  simpa using h

end Formalism.ZeroFreeDirichlet
