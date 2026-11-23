import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LFamPos

theorem norm_lamChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  refine le_trans ?_ (𝓕.lam_le n)
  unfold LFam.lamChi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.lam_nonneg g n)]

theorem summable_lamChi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (𝓕.lamChi χ) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (2 : ℂ)
  refine Summable.of_norm_bounded h.norm fun n => ?_
  refine LSeries.norm_term_le s ?_
  refine (norm_lamChi_le 𝓕 χ n).trans (le_of_eq ?_)
  simp [abs_of_nonneg vonMangoldt_nonneg]

theorem hasSum_re (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (u : ℂ) (hs : 1 < σ) (hu : u.re = 0) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g * (n : ℂ) ^ (-u)).re)
      (LSeries (𝓕.lamChi χ) (σ + u)).re := by
  have h := (summable_lamChi 𝓕 χ (s := σ + u) (by simpa [hu] using hs)).hasSum
  have h2 := Complex.hasSum_re h
  convert h2 using 2 with n
  · by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn, LFam.lamChi, Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [if_neg hn, ← Complex.re_ofReal_mul]
      congr 1
      rw [div_eq_mul_inv, ← cpow_neg, neg_add, cpow_add _ _ hn']
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
  · rfl

theorem hasSum_re₀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (hs : 1 < σ) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g).re)
      (LSeries (𝓕.lamChi χ) σ).re := by
  simpa using hasSum_re 𝓕 χ σ 0 hs rfl

theorem w_nonneg (𝓕 : LFam) (σ : ℝ) (n : ℕ) (g : 𝓕.G) :
    0 ≤ (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (𝓕.lam_nonneg g n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem pm_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := congrArg (fun φ : AddChar G ℂ => φ g) h
    simpa using this
  exact mul_self_eq_one_iff.mp this

theorem trig (z : ℂ) (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z * z).re := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

theorem positivity : ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (σ t : ℝ), 1 < σ → 0 ≤ 3 * (LSeries (𝓕.lamChi 1) σ).re + 4 * (LSeries (𝓕.lamChi χ) (σ + t * I)).re + (LSeries (𝓕.lamChi (χ * χ)) (σ + 2 * t * I)).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re ∧ (χ * χ = 1 → ψ * ψ = 1 → 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re + (LSeries (𝓕.lamChi ψ) σ).re + (LSeries (𝓕.lamChi (χ * ψ)) σ).re) := by
  intro 𝓕 χ ψ σ t hσ
  have h1 := hasSum_re₀ 𝓕 1 σ hσ
  refine ⟨?_, ?_, fun hχ hψ => ⟨?_, ?_⟩⟩
  · have h2 := hasSum_re 𝓕 χ σ (t * I) hσ (by simp)
    have h3 := hasSum_re 𝓕 (χ * χ) σ (2 * t * I) hσ (by simp)
    refine HasSum.nonneg (fun n => ?_) (((h1.mul_left 3).add (h2.mul_left 4)).add h3)
    by_cases hn : n = 0
    · simp [hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hz : ‖χ g * (n : ℂ) ^ (-(t * I))‖ = 1 := by
      rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have ht := trig _ hz
    have he : (χ * χ) g * (n : ℂ) ^ (-(2 * t * I)) = (χ g * (n : ℂ) ^ (-(t * I))) * (χ g * (n : ℂ) ^ (-(t * I))) := by
      rw [show -(2 * (t : ℂ) * I) = -(t * I) + -(t * I) by ring, cpow_add _ _ hn', AddChar.mul_apply]
      ring
    rw [he, AddChar.one_apply, Complex.one_re]
    have := mul_nonneg (w_nonneg 𝓕 σ n g) ht
    linarith
  · refine HasSum.nonneg (fun n => Finset.sum_nonneg fun g _ => ?_) h1
    rw [AddChar.one_apply, Complex.one_re, mul_one]
    exact w_nonneg 𝓕 σ n g
  · refine HasSum.nonneg (fun n => ?_) (h1.add (hasSum_re₀ 𝓕 χ σ hσ))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply]
    rcases pm_one χ hχ g with h | h <;> rw [h] <;> simp only [one_re, neg_re] <;> linarith
  · refine HasSum.nonneg (fun n => ?_) (((h1.add (hasSum_re₀ 𝓕 χ σ hσ)).add (hasSum_re₀ 𝓕 ψ σ hσ)).add (hasSum_re₀ 𝓕 (χ * ψ) σ hσ))
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply, AddChar.mul_apply]
    rcases pm_one χ hχ g with h | h <;> rcases pm_one ψ hψ g with h' | h' <;> rw [h, h'] <;>
      simp only [one_re, neg_re, mul_one, mul_neg, neg_neg] <;> linarith

end GlobalTheory.Hk.LFamPos
