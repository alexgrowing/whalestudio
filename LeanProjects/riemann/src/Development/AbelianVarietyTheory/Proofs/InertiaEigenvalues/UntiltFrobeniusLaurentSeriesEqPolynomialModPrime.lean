import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffHasSumUntiltFrobeniusCombinationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAroundLastMaxNullSequenceStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PolyRoot

theorem key_exp (l : ℕ) [Fact l.Prime] (h : ℕ) (P : ℝ) (hP : 0 < P) (k : ℤ) :
    P ^ ((l:ℝ) ^ k) * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P ^ ((l:ℝ) ^ (k + h)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_add hP, zpow_add₀ hl, zpow_natCast]
  congr 1; ring

theorem rho_pow (l : ℕ) [Fact l.Prime] (h D n : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ n) = P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ ((n:ℤ) - D)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_natCast, ← Real.rpow_mul hP, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
  congr 1; push_cast; ring

theorem poly_root_mod_l : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (σ : Fl l), 1 ≤ h → μ ≠ 0 → sh σ = l → ∃ (t : ℂ_[l]) (D E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), t ≠ 0 ∧ M + h ≤ E ∧ (∀ k, k ≤ E → ‖a k‖ ≤ 1) ∧ ‖a (M + h)‖ = 1 ∧ ‖(l : ℂ_[l])‖ ≤ ρ ∧ ρ < 1 ∧ ‖(l : ℂ_[l])‖ * ρ ^ l ^ D = ‖(l : ℂ_[l])‖ ^ l ^ h ∧ ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ ∧ (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) ∧ ∀ u : Fl l, ‖∑ i : Fin h, μ i * lam h i (σ * u ^ l ^ D) - t * ∑ k ∈ Finset.range (E + 1), a k * sh u ^ l ^ k‖ ≤ ‖(l : ℂ_[l])‖ * ‖t‖ := by
  intro l _ h μ σ h1 hμ hσ
  obtain ⟨pwadd, pwmul, pwzero, pwcomp, pwnat, pwpow, pwnorm⟩ := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨m, hm, ⟨k0, hk0⟩, hsum⟩ := GlobalTheory.T.exists_coeff_hasSum_untiltFrobeniusCombination l h μ h1 hμ
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = ‖(l : ℂ_[l])‖ := ⟨_, rfl⟩
  rw [← hPd]
  have hP0 : 0 < P := hPd ▸ norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hP1 : P < 1 := hPd ▸ GlobalTheory.RingBasics.norm_p_lt
  have hσn : ‖sh σ‖ = P := by rw [hσ, hPd]
  obtain ⟨α, hα⟩ : ∃ α : ℤ → ℂ_[l], ∀ k, α k = m k * sh (pw k σ) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℤ → ℝ, ∀ k, β k = ‖α k‖ := ⟨_, fun _ => rfl⟩
  have hshσ : ∀ k : ℤ, ‖sh (pw k σ)‖ = P ^ ((l:ℝ) ^ k) := fun k => by rw [pwnorm, hσn]
  have hβ : ∀ k, β k = ‖m k‖ * P ^ ((l:ℝ) ^ k) := fun k => by
    rw [hβd, hα, norm_mul, hshσ]
  have hkey : ∀ k : ℤ, β k * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P * β (k + h) := fun k => by
    rw [hβ, hβ, hm k, norm_mul, ← hPd, ← key_exp l h P hP0 k]; ring
  have hσlt : ‖sh σ‖ < 1 := hσn ▸ hP1
  have hαsum : Summable α := by
    have := (hsum σ hσlt).summable
    rwa [show (fun k : ℤ => m k * sh (pw k σ)) = α from funext fun k => (hα k).symm] at this
  have hβt : Filter.Tendsto β Filter.cofinite (nhds 0) := by
    have := (hαsum.tendsto_cofinite_zero).norm
    rw [norm_zero] at this
    rwa [show (fun k => ‖α k‖) = β from funext fun k => (hβd k).symm] at this
  have hβne : ∃ k, β k ≠ 0 := ⟨k0, by
    rw [hβ]; exact mul_ne_zero (norm_ne_zero_iff.2 hk0) (Real.rpow_pos_of_pos hP0 _).ne'⟩
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by rw [hβd]; exact norm_nonneg _
  obtain ⟨D, E, M, hD, hME, hpos, hmax, hstrict, htail⟩ :=
    GlobalTheory.T.window_around_last_max_null_sequence β P h hP0 hβ0 hβne hβt
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ((M + h : ℕ) : ℤ) - D := ⟨_, rfl⟩
  rw [← hN] at hpos hmax hstrict htail
  have htn : ‖α N‖ = β N := (hβd N).symm
  have ht0 : α N ≠ 0 := by intro h0; rw [← norm_eq_zero, htn] at h0; linarith
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hlD : (0:ℝ) < (l:ℝ) ^ D := by positivity
  have hnorm_a : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ = β ((k:ℤ) - D) / β N := fun k => by
    rw [norm_div, htn, ← hβd]
  have hprod : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ * (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ k)
      = P * β ((k:ℤ) - D + h) / β N := fun k => by
    rw [hnorm_a, rho_pow l h D k P hP0.le, div_mul_eq_mul_div, hkey]
  refine ⟨α N, D, E, M, fun k : ℕ => α ((k:ℤ) - D) / α N, P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D),
    ht0, hME, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _
    show ‖α ((k:ℤ) - D) / α N‖ ≤ 1
    rw [hnorm_a, div_le_one hpos]; exact hmax _
  · show ‖α (((M + h : ℕ) : ℤ) - D) / α N‖ = 1
    rw [← hN, div_self ht0, norm_one]
  · have he : ((l:ℝ) ^ h - 1) / (l:ℝ) ^ D ≤ 1 := by
      rw [div_le_one hlD]
      have : (l:ℝ) ^ h ≤ (l:ℝ) ^ D := pow_le_pow_right₀ (by linarith) hD
      linarith
    calc P = P ^ (1:ℝ) := (Real.rpow_one P).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hP0 hP1.le he
  · have hq : (l:ℝ) ≤ (l:ℝ) ^ h := le_self_pow₀ (by linarith) (by omega)
    exact Real.rpow_lt_one hP0.le hP1 (div_pos (by linarith) hlD)
  · rw [rho_pow l h D D P hP0.le, sub_self, zpow_zero, mul_one, ← Real.rpow_natCast P (l ^ h)]
    rw [show P * P ^ ((l:ℝ) ^ h - 1) = P ^ ((1:ℝ) + ((l:ℝ) ^ h - 1)) by
      rw [Real.rpow_add hP0, Real.rpow_one]]
    congr 1; push_cast; ring
  · show ‖α ((M:ℤ) - D) / α N‖ * _ = P
    rw [hprod, show (M:ℤ) - D + h = N by rw [hN]; push_cast; ring, mul_div_assoc,
      div_self hpos.ne', mul_one]
  · intro k hk _
    show ‖α ((k:ℤ) - D) / α N‖ * _ < P
    rw [hprod, div_lt_iff₀ hpos]
    exact mul_lt_mul_of_pos_left (hstrict _ (by omega)) hP0
  · intro u
    have hx : ‖sh (σ * u ^ l ^ D)‖ < 1 := by
      rw [shmul, shpow, norm_mul, norm_pow, hσn]
      calc P * ‖sh u‖ ^ l ^ D ≤ P * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (shle u)) hP0.le
        _ < 1 := by rw [mul_one]; exact hP1
    have hS := hsum _ hx
    have hf : ∀ k : ℤ, m k * sh (pw k (σ * u ^ l ^ D)) = α k * sh (pw (k + D) u) := fun k => by
      rw [hα, pwmul, ← pwnat D u, ← pwcomp, shmul]; ring
    rw [show (fun k : ℤ => m k * sh (pw k (σ * u ^ l ^ D))) = fun k => α k * sh (pw (k + D) u)
      from funext hf] at hS
    have htr := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℤ (fun k => α k * sh (pw (k + D) u)) _
      ((Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D)) (P * ‖α N‖)
      (mul_nonneg hP0.le (norm_nonneg _)) hS (by
        intro j hj
        have hj' : j < -(D:ℤ) ∨ (E:ℤ) - D < j := by
          by_contra hc
          push_neg at hc
          apply hj
          rw [Finset.mem_image]
          exact ⟨(j + D).toNat, Finset.mem_range.2 (by omega), by omega⟩
        show ‖α j * sh (pw (j + D) u)‖ ≤ P * ‖α N‖
        rw [norm_mul, ← hβd, htn]
        exact (mul_le_of_le_one_right (hβ0 j) (shle _)).trans (htail j hj'))
    have heq : ∑ j ∈ (Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D), α j * sh (pw (j + D) u)
        = α N * ∑ k ∈ Finset.range (E + 1), α ((k:ℤ) - D) / α N * sh u ^ l ^ k := by
      rw [Finset.sum_image (fun x _ y _ hxy => by simpa using hxy), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_add_cancel, pwnat, shpow]
      field_simp
    rw [heq] at htr
    exact htr

end GlobalTheory.PolyRoot
