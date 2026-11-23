import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHBSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSum

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem pow_absorb (N : ℕ) (c l large₂ : ℝ) (hc : 0 < c) (hl : 2 ≤ l)
    (hL : 2 * N / c * l * Real.log (l + 2) ≤ large₂) :
    l ^ N * Real.exp (-(c / 2 * large₂ / l)) ≤ 1 := by
  have hl0 : 0 < l := by linarith
  have hpow : Real.exp (N * Real.log l) = l ^ N := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hl0 N)]
  have key : (N : ℝ) * Real.log l ≤ c / 2 * large₂ / l := by
    rw [le_div_iff₀ hl0]
    have hlog : Real.log l ≤ Real.log (l + 2) := Real.log_le_log hl0 (by linarith)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc (N : ℝ) * Real.log l * l ≤ N * Real.log (l + 2) * l := by gcongr
      _ = c / 2 * (2 * N / c * l * Real.log (l + 2)) := by field_simp
      _ ≤ c / 2 * large₂ := by gcongr
  calc l ^ N * Real.exp (-(c / 2 * large₂ / l))
      = Real.exp (N * Real.log l + -(c / 2 * large₂ / l)) := by rw [Real.exp_add, hpow]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem zero_sum_bound_lossy : ZeroSumOfB := by
  intro hLD hDH
  obtain ⟨a, B, C, ha, hB, hC, hdens⟩ := density_norm hLD
  obtain ⟨c₀, c₁, c₂, N, hc₀, hc₁, hc₂, hdh⟩ := hDH
  refine ⟨min c₀ (1 / 20), lt_min hc₀ (by norm_num), min_le_right _ _, ?_⟩
  intro C₁ A₁ hA₁
  have hk : 0 < A₁ + 2 := by linarith
  have hcZ := cZ_pos
  have hcZ' := cZ_le
  set η0 : ℝ := min (cZ / 2) (c₁ / (A₁ + 2)) with hη0
  have hη0pos : 0 < η0 := lt_min (by linarith) (by positivity)
  have hη0a : η0 ≤ cZ / 2 := min_le_left _ _
  have hη0b : η0 ≤ c₁ / (A₁ + 2) := min_le_right _ _
  have hη0c : η0 ≤ c₁ := hη0b.trans (div_le_self hc₁.le (by linarith))
  have hη01 : η0 ≤ 1 := by linarith
  set A' : ℝ := 4 * |C₁| * C * Real.exp (a + a * cZ / 2) * (A₁ + 2) ^ (B + 1) with hA'
  have hA'0 : 0 ≤ A' := by
    have h1 : 0 ≤ (A₁ + 2) ^ (B + 1) := Real.rpow_nonneg hk.le _
    have h2 : 0 ≤ C := by linarith
    positivity
  set c : ℝ := cZ / (4 * (A₁ + 2)) with hc
  have hc0 : 0 < c := by positivity
  set K0 : ℝ := (A₁ + 2) * (a + 1 + 2 / c₂) + (B + 1) / c with hK0
  have hK00 : 0 ≤ K0 := by
    have h1 : 0 ≤ a + 1 + 2 / c₂ := by positivity
    have h2 : 0 ≤ (B + 1) / c := by positivity
    positivity
  refine ⟨c / 2, A' * (A₁ + 2) ^ N / η0, K0 + 2 * N / c, by positivity, ?_⟩
  intro M _ Z m h8 hZ _ hms hwin y hy hL
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8' : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM0 : (0 : ℝ) < M := by linarith
  have hpw : 0 < (M : ℝ) ^ A₁ := Real.rpow_pos_of_pos hM0 _
  obtain ⟨hl2, hlℓ, hℓk⟩ := ell_bounds M hM8 A₁ hA₁
  set ℓ : ℝ := Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓN : 1 ≤ ℓ ^ N := one_le_pow₀ hℓ1
  have hll : 0 ≤ Real.log M * Real.log (Real.log M + 2) :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hL1 : K0 * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    have : 0 ≤ 2 * N / c * (Real.log M * Real.log (Real.log M + 2)) :=
      mul_nonneg (by positivity) hll
    nlinarith
  have hL2 : 2 * N / c * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    have : 0 ≤ K0 * (Real.log M * Real.log (Real.log M + 2)) := mul_nonneg hK00 hll
    nlinarith
  have habs := pow_absorb N c (Real.log M) (Real.log y) hc0 hl2 hL2
  suffices h : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) by
    obtain ⟨θ, h0, h1, hη, hθ⟩ := h
    have key := zeroSum_core a B C ha hB hC hdens (min c₀ (1 / 20)) c₂ C₁ A₁ (min_le_right _ _) hc₂ hA₁
      M Z m h8 hZ hms hwin y hy hL1 θ h0 h1 hθ
    refine key.trans ?_
    have hηpos : 0 < etaOf M := etaOf_pos M (by omega)
    set E : ℝ := Real.exp (-(c / 2 * Real.log y / Real.log M)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hEE : Real.exp (-(c * Real.log y / Real.log M)) = E * E := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring
    rw [hEE]
    have hpow : ℓ ^ N ≤ (A₁ + 2) ^ N * Real.log M ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hℓ0.le hℓk N
    have hθle : θ ≤ etaOf M * ((A₁ + 2) ^ N * Real.log M ^ N) / η0 := by
      rw [le_div_iff₀ hη0pos]
      calc θ * η0 = η0 * θ := by ring
        _ ≤ etaOf M * ℓ ^ N := hη
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hηpos.le
    have hkN : 0 ≤ (A₁ + 2) ^ N := by positivity
    calc A' * θ * (E * E)
        ≤ A' * (etaOf M * ((A₁ + 2) ^ N * Real.log M ^ N) / η0) * (E * E) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hθle hA'0
      _ = (A' * (A₁ + 2) ^ N / η0 * etaOf M * E) * (Real.log M ^ N * E) := by ring
      _ ≤ (A' * (A₁ + 2) ^ N / η0 * etaOf M * E) * 1 := by
          apply mul_le_mul_of_nonneg_left habs
          positivity
      _ = _ := by ring
  have hone' : η0 ≤ etaOf M * ℓ ^ N → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) := by
    intro hη
    refine ⟨1, one_pos, le_refl _, by linarith, ?_⟩
    intro χ ρ _ hr
    unfold InRegion at hr
    replace hr := not_le.mp hr
    have habs := abs_nonneg ρ.im
    have h1 : (1 : ℝ) ≤ (M : ℝ) * (|ρ.im| + 2) := by nlinarith
    have h2 : 0 ≤ cZ / Real.log ((M : ℝ) * (|ρ.im| + 2)) := div_nonneg hcZ.le (Real.log_nonneg h1)
    have h3 : 0 ≤ ℓ * (1 - ρ.re) := mul_nonneg hℓ0.le (by linarith)
    simpa using h3
  have hone : η0 ≤ etaOf M → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) := by
    intro hη
    apply hone'
    calc η0 ≤ etaOf M := hη
      _ = etaOf M * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hℓN (hη0pos.le.trans hη)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · apply hone
    rw [etaOf_none M he]
    exact hη01
  · obtain ⟨hsq, hne, hL0, _, hβ1⟩ := eOf_exc M (χ₁, β₁) he
    simp only at hsq hne hL0 hβ1
    have hβ : 0 < 1 - β₁ := by linarith
    have hlow : (1 - β₁) * ℓ / (A₁ + 2) ≤ (1 - β₁) * Real.log M := by
      rw [div_le_iff₀ hk]
      calc (1 - β₁) * ℓ ≤ (1 - β₁) * ((A₁ + 2) * Real.log M) := mul_le_mul_of_nonneg_left hℓk hβ.le
        _ = _ := by ring
    have hup : (1 - β₁) * ℓ ^ N ≤ (1 - β₁) * Real.log M * ℓ ^ N := by
      have h0 : 0 ≤ (1 - β₁) * ℓ ^ N := by positivity
      calc (1 - β₁) * ℓ ^ N = (1 - β₁) * ℓ ^ N * 1 := (mul_one _).symm
        _ ≤ (1 - β₁) * ℓ ^ N * Real.log M := mul_le_mul_of_nonneg_left (by linarith) h0
        _ = _ := by ring
    by_cases hr : InRegion cZ M (β₁ : ℂ)
    · by_cases hcc : c₁ ≤ (1 - β₁) * ℓ
      · apply hone
        rw [etaOf_some M χ₁ β₁ he]
        apply le_min hη01
        have : c₁ / (A₁ + 2) ≤ (1 - β₁) * ℓ / (A₁ + 2) := div_le_div_of_nonneg_right hcc hk.le
        linarith
      · replace hcc := not_le.mp hcc
        by_cases hu : c₁ ≤ (1 - β₁) * ℓ ^ N
        · apply hone'
          rw [etaOf_some M χ₁ β₁ he, min_mul_of_nonneg (1 : ℝ) ((1 - β₁) * Real.log M) (by positivity : (0 : ℝ) ≤ ℓ ^ N)]
          apply le_min
          · linarith
          · linarith
        · replace hu := not_le.mp hu
          have hθ0 : 0 < (1 - β₁) * ℓ ^ N / c₁ := by positivity
          have hθ1 : (1 - β₁) * ℓ ^ N / c₁ ≤ 1 := by
            rw [div_le_one hc₁]; exact hu.le
          refine ⟨(1 - β₁) * ℓ ^ N / c₁, hθ0, hθ1, ?_, ?_⟩
          · rw [etaOf_some M χ₁ β₁ he, min_mul_of_nonneg (1 : ℝ) ((1 - β₁) * Real.log M) (by positivity : (0 : ℝ) ≤ ℓ ^ N)]
            apply le_min
            · calc η0 * ((1 - β₁) * ℓ ^ N / c₁) ≤ 1 * 1 := mul_le_mul hη01 hθ1 hθ0.le zero_le_one
                _ ≤ 1 * ℓ ^ N := by linarith
            · calc η0 * ((1 - β₁) * ℓ ^ N / c₁) ≤ c₁ * ((1 - β₁) * ℓ ^ N / c₁) :=
                    mul_le_mul_of_nonneg_right hη0c hθ0.le
                _ = (1 - β₁) * ℓ ^ N := by field_simp
                _ ≤ _ := hup
          · intro χ ρ hρ hnr
            obtain ⟨hz, hre, him⟩ := hZ χ ρ hρ
            have hd := hdh M χ₁ χ β₁ ((M : ℝ) ^ A₁ + 3) ρ (by omega) (by linarith) hsq hne hL0
              (by
                have : 1 - β₁ < c₁ / ℓ := by rw [lt_div_iff₀ hℓ0]; exact hcc
                linarith)
              hβ1 hz
              (by
                have := min_le_left c₀ (1 / 20 : ℝ)
                linarith)
              (by linarith)
              (by
                intro heq
                have h2 : ρ = (β₁ : ℂ) := (Prod.mk.inj heq).2
                rw [h2] at hnr
                exact hnr hr)
            rw [one_div_div]
            rw [div_le_iff₀ hℓ0] at hd
            linarith
    · apply hone
      have := etaOf_far M (by omega) χ₁ β₁ he hr
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
