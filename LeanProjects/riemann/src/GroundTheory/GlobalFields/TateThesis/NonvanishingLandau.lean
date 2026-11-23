import Mathlib
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
import GroundTheory.GlobalFields.TateThesis.NonvanishingDivisorSum

open NumberField InfinitePlace IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Complex Topology
  Filter Ideal
open scoped ComplexOrder

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

variable (K) in

theorem continuedDedekindZeta_neg_two : continuedDedekindZeta K (-2) = 0 := by
  rw [continuedDedekindZeta_of_ne_zero K (by norm_num), normalizedDedekindZeta]
  have hR : Gammaℝ (-2) = 0 := Gammaℝ_eq_zero_iff.2 ⟨1, by norm_num⟩
  have hC : Gammaℂ (-2) = 0 := by
    rw [Gammaℂ_def, show (-2 : ℂ) = -((2 : ℕ) : ℂ) by norm_num, Complex.Gamma_neg_nat_eq_zero,
      mul_zero]
  have hcard : 0 < nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have h0 : Gammaℝ (-2) ^ nrRealPlaces K * Gammaℂ (-2) ^ nrComplexPlaces K = 0 := by
    rcases Nat.eq_zero_or_pos (nrRealPlaces K) with h | h
    · rw [hC, zero_pow (by omega), mul_zero]
    · rw [hR, zero_pow h.ne', zero_mul]
  rw [h0, inv_zero, mul_zero, zero_mul]

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def twistCoeff (t : ℝ) (J : Ideal (𝓞 K)) : ℂ :=
  χ.coeff J * (absNorm J : ℂ) ^ (-((t : ℂ) * I))

theorem twistCoeff_mul (t : ℝ) (A B : Ideal (𝓞 K)) :
    χ.twistCoeff t (A * B) = χ.twistCoeff t A * χ.twistCoeff t B := by
  rw [twistCoeff, twistCoeff, twistCoeff, coeff_mul, map_mul, Nat.cast_mul,
    natCast_mul_natCast_cpow]
  ring

theorem twistCoeff_top (t : ℝ) : χ.twistCoeff t ⊤ = 1 := by
  rw [twistCoeff, coeff_top, absNorm_top, Nat.cast_one, one_cpow, one_mul]

theorem twistCoeff_bot (t : ℝ) : χ.twistCoeff t ⊥ = 0 := by
  rw [twistCoeff, coeff_bot, zero_mul]

theorem norm_twistCoeff_le (t : ℝ) (J : Ideal (𝓞 K)) : ‖χ.twistCoeff t J‖ ≤ 1 := by
  by_cases hJ : J = ⊥
  · rw [hJ, twistCoeff_bot, norm_zero]
    exact zero_le_one
  have hN : 0 < absNorm J := Nat.pos_of_ne_zero fun h ↦ hJ (absNorm_eq_zero_iff.1 h)
  rw [twistCoeff, norm_mul, norm_natCast_cpow_neg_mul_I hN, mul_one]
  exact χ.norm_coeff_le J

theorem hasSum_twistCoeff (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun J ↦ χ.twistCoeff t J * (absNorm J : ℂ) ^ (-s)) (χ.LFunction (s + t * I)) := by
  have hs' : 1 < (s + t * I).re := by simpa using hs
  refine (χ.hasSum_LFunction hs').congr_fun fun J ↦ ?_
  by_cases hJ : J = ⊥
  · rw [hJ, twistCoeff_bot, coeff_bot, zero_mul, zero_mul]
  have hN : (absNorm J : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun h ↦ hJ (absNorm_eq_zero_iff.1 h)
  rw [twistCoeff, neg_add, cpow_add _ _ hN]
  ring

theorem twistCoeff_asIdeal_of_not_dvd (t : ℝ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {π : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    χ.twistCoeff t v.asIdeal = χ.toIdele (finiteEmbedding v π) *
      ((ideleModule K (finiteEmbedding v π) : ℝ) : ℂ) ^ ((t : ℂ) * I) :=
  χ.coeff_mul_cpow_eq hv hπ t

theorem exists_real_twistCoeff (t : ℝ)
    (hsq : ∀ x : IdeleGroup K,
      ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1)
    (J : Ideal (𝓞 K)) : ∃ r : ℝ, χ.twistCoeff t J = r := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact ⟨0, by rw [Ideal.zero_eq_bot, twistCoeff_bot, ofReal_zero]⟩
  | h₂ x hx => exact ⟨1, by rw [Ideal.isUnit_iff.1 hx, twistCoeff_top, ofReal_one]⟩
  | h₃ a p _ hp ih =>
    obtain ⟨r, hr⟩ := ih
    rw [twistCoeff_mul, hr]
    let v : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hvp : v.asIdeal = p := rfl
    by_cases hv : v.asIdeal ∣ χ.conductor
    · refine ⟨0, ?_⟩
      rw [← hvp, twistCoeff, χ.coeff_asIdeal_of_dvd hv, zero_mul, zero_mul, ofReal_zero]
    · obtain ⟨π, hπ⟩ := exists_uniformizer v
      have h := hsq (finiteEmbedding v π)
      rw [← χ.twistCoeff_asIdeal_of_not_dvd t hv hπ, hvp, sq, mul_self_eq_one_iff] at h
      rcases h with h | h
      · exact ⟨r, by rw [h, one_mul]⟩
      · exact ⟨-r, by rw [h, ofReal_neg, neg_one_mul]⟩

def twistCoeffRe (t : ℝ) (J : Ideal (𝓞 K)) : ℝ :=
  (χ.twistCoeff t J).re

theorem ofReal_twistCoeffRe (t : ℝ)
    (hsq : ∀ x : IdeleGroup K,
      ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1)
    (J : Ideal (𝓞 K)) : (χ.twistCoeffRe t J : ℂ) = χ.twistCoeff t J := by
  obtain ⟨r, hr⟩ := χ.exists_real_twistCoeff t hsq J
  rw [twistCoeffRe, hr, ofReal_re]

theorem continuation_ne_zero_of_sq_eq_one (t : ℝ)
    (hsq : ∀ x : IdeleGroup K,
      ((χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ ((t : ℂ) * I)) ^ 2 = 1)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hGL : ∀ s : ℂ, 1 < s.re → G s = χ.LFunction s) :
    G (1 + t * I) ≠ 0 := by
  intro hG0
  classical
  set ψ : Ideal (𝓞 K) → ℝ := χ.twistCoeffRe t with hψ_def
  have hψc : ∀ J, (ψ J : ℂ) = χ.twistCoeff t J := χ.ofReal_twistCoeffRe t hsq
  have hψmul : ∀ A B, ψ (A * B) = ψ A * ψ B := fun A B ↦ by
    apply ofReal_injective
    rw [ofReal_mul, hψc, hψc, hψc, twistCoeff_mul]
  have hψ1 : ψ ⊤ = 1 := by
    apply ofReal_injective
    rw [hψc, twistCoeff_top, ofReal_one]
  have hψb : ∀ A, |ψ A| ≤ 1 := fun A ↦ by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hψc]
    exact χ.norm_twistCoeff_le t A

  have hψL : ∀ s : ℂ, 1 < s.re →
      ∑' J, (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s) = χ.LFunction (s + t * I) := fun s hs ↦ by
    simp only [hψc]
    exact (χ.hasSum_twistCoeff t hs).tsum_eq

  set g₁ : ℂ → ℂ := fun s ↦ G (s + t * I) with hg₁_def
  have hg₁ : Differentiable ℂ g₁ := hG.comp (differentiable_id.add_const _)
  have hg₁1 : g₁ 1 = 0 := hG0
  set ρ : ℂ := (dedekindZeta_residue K : ℂ) with hρ
  set F : ℂ → ℂ := Function.update (fun s ↦ continuedDedekindZeta K s * g₁ s) 1
    (ρ * deriv g₁ 1) with hF_def
  have hFne : ∀ s, s ≠ 1 → DifferentiableAt ℂ F s := fun s hs ↦ by
    refine ((differentiableAt_continuedDedekindZeta K hs).mul (hg₁ s)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hs] with z hz using Function.update_of_ne hz ..
  have hFdiff : Differentiable ℂ F := by
    intro s
    rcases ne_or_eq s 1 with hs | rfl
    · exact hFne s hs
    refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz using hFne z hz
    set Gz : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * continuedDedekindZeta K s) 1 ρ with hGz
    set H : ℂ → ℂ := Function.update (fun s ↦ (g₁ s - g₁ 1) / (s - 1)) 1 (deriv g₁ 1) with hH
    have hFGH : F = Gz * H := by
      ext z
      rcases eq_or_ne z 1 with rfl | hz
      · simp only [hF_def, hGz, hH, Pi.mul_apply, Function.update_self]
      · simp only [hF_def, hGz, hH, Pi.mul_apply, Function.update_of_ne hz, hg₁1, sub_zero]
        field_simp [sub_ne_zero.2 hz]
    rw [hFGH]
    refine ContinuousAt.mul ?_ (hg₁ 1).hasDerivAt.continuousAt_div
    rw [hGz, continuousAt_update_same]
    exact tendsto_sub_one_mul_continuedDedekindZeta K

  have hF2 : F ((-2 : ℝ) : ℂ) = 0 := by
    have h : ((-2 : ℝ) : ℂ) = -2 := by push_cast; ring
    rw [h, hF_def, Function.update_of_ne (by norm_num), continuedDedekindZeta_neg_two, zero_mul]

  have hFL : {s : ℂ | (1 : ℝ) < s.re}.EqOn F (LSeries (divisorSumCoeff ψ)) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h ↦ by
      rw [Set.mem_ofPred_eq, h, one_re] at hs
      exact lt_irrefl _ hs
    have hs' : 1 < (s + t * I).re := by simpa using hs
    rw [hF_def, Function.update_of_ne hs1, LSeries,
      (hasSum_LSeries_term_divisorSum hψb hs).tsum_eq, hψL s hs, continuedDedekindZeta_eq K hs]
    simp only [hg₁_def]
    rw [hGL _ hs']
    ring
  have habs : LSeries.abscissaOfAbsConv (divisorSumCoeff ψ) ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
      (hasSum_LSeries_term_divisorSum hψb (by simpa using hy)).summable
  have hpos := LSeries.positive_of_differentiable_of_eqOn
    (fun n ↦ divisorSumCoeff_nonneg hψmul hψ1 hψb n)
    (by rw [divisorSumCoeff_one, hψ1, ofReal_one]; exact zero_lt_one) hFdiff habs hFL (-2)
  rw [hF2] at hpos
  exact lt_irrefl _ hpos

end HeckeCharacter

end

end GroundTheory.Global
