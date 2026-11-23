import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.TorsionNormIteration.LubinTateExample

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.HondaFunEq

variable {K : Type} [NormedField K]

theorem sq_apply (σ : K →+* K) (a : K) : (σ ^ 2) a = σ (σ a) := by
  rw [pow_two]; rfl

theorem frobLift_sq [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} (h : Unr K l σ) :
    Formalism.G.IsFrobLift l (l ^ 2) (σ ^ 2) := by
  obtain ⟨-, -, -, hmax, hiso, hfrob⟩ := h
  have key : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ ≤ ‖(l : K)‖ := fun x hx => hmax _ (hfrob x hx)
  intro a ha
  have hsa : ‖σ a‖ ≤ 1 := by rw [hiso]; exact ha
  have hal : ‖a ^ l‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have hd : (σ ^ 2) a - a ^ (l ^ 2) = (σ (σ a) - (σ a) ^ l) + ((σ a) ^ l - (a ^ l) ^ l) := by
    rw [sq_apply, ← pow_mul, sq]; ring
  rw [hd]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key _ hsa) ?_)
  rw [← (Commute.all (σ a) (a ^ l)).geom_sum₂_mul, norm_mul]
  have hs : ‖∑ i ∈ Finset.range l, σ a ^ i * (a ^ l) ^ (l - 1 - i)‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_mul, norm_pow, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hsa) (by positivity) (pow_le_one₀ (norm_nonneg _) hal)
  calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul hs (key a ha) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem setting [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} (h : Unr K l σ) :
    Formalism.G.FunctionalEquationSetting K l (l ^ 2) (σ ^ 2) :=
  ⟨h.1, ⟨2, by norm_num, rfl⟩, h.2.2.1, frobLift_sq h⟩

theorem coeff_ltLog_pow (l : ℕ) (hl : 2 ≤ l) (j : ℕ) :
    coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
  have h : ∃ i : ℕ, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
  simp only [ltLog, coeff_mk, dif_pos h]
  have hq : 2 ≤ l ^ 2 := le_trans hl (Nat.le_self_pow (by norm_num) l)
  have := Nat.find_spec h
  rw [(Nat.pow_right_injective hq this).symm]

theorem coeff_ltLog_of_not (l : ℕ) {n : ℕ} (h : ¬ ∃ j : ℕ, n = (l ^ 2) ^ j) :
    coeff n (ltLog K l) = 0 := by
  simp only [ltLog, coeff_mk, dif_neg h]

theorem ltLog_funEq [CharZero K] (l : ℕ) (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ (ltLog K l)).subst ((X : K⟦X⟧) ^ (l ^ 2)) = X := by
  have hq : l ^ 2 ≠ 0 := by positivity
  have hq2 : 2 ≤ l ^ 2 := le_trans hl (Nat.le_self_pow (by norm_num) l)
  have hmap : PowerSeries.map τ (ltLog K l) = ltLog K l := by
    ext n
    simp only [coeff_map, ltLog, coeff_mk]
    split_ifs <;> simp [map_inv₀]
  rw [hmap, ← PowerSeries.expand_apply _ hq]
  ext n
  rw [map_sub, coeff_smul, PowerSeries.coeff_expand, coeff_X, smul_eq_mul]
  by_cases hn : ∃ j : ℕ, n = (l ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    cases j with
    | zero =>
      have : ¬ l ^ 2 ∣ 1 := fun h => by
        have := Nat.le_of_dvd one_pos h; omega
      rw [coeff_ltLog_pow l hl 0, if_neg (by simpa using this), if_pos (pow_zero _)]; simp
    | succ k =>
      have h1 : (l ^ 2) ^ (k + 1) ≠ 1 := by
        exact (Nat.one_lt_pow (Nat.succ_ne_zero k) (by omega : 1 < l ^ 2)).ne'
      rw [if_pos (dvd_pow_self _ (Nat.succ_ne_zero k)), if_neg h1, pow_succ,
        Nat.mul_div_cancel _ (by omega), coeff_ltLog_pow l hl k, ← pow_succ, coeff_ltLog_pow l hl (k + 1)]
      have hl0 : (l : K) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
      field_simp
      ring
  · have h1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
    rw [coeff_ltLog_of_not l hn, if_neg h1]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      have : ¬ ∃ j : ℕ, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj]; ring⟩
      rw [Nat.mul_div_cancel_left _ (by omega), coeff_ltLog_of_not l this]; simp
    · simp

theorem funEq_scaled [IsUltrametricDist K] {l : ℕ} {σ : K →+* K} {f : K⟦X⟧} {c ε : K} (hε : ‖ε‖ = 1)
    (hc : ε = c * (σ ^ 2) ε)
    (hH : CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f)) (hl : (l : K) ≠ 0) :
    Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) (ε⁻¹ • f) := by
  set τ := σ ^ 2 with hτdef
  have hq : l ^ 2 ≠ 0 := by
    have hl' : l ≠ 0 := by rintro rfl; simp at hl
    exact pow_ne_zero 2 hl'
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hτε : τ ε ≠ 0 := (map_ne_zero τ).2 hε0
  have hτ : τ ε⁻¹ = c * ε⁻¹ := by
    rw [map_inv₀]
    field_simp
    linear_combination hc
  have hfrob : frobOp τ (l ^ 2) 1 f = PowerSeries.expand (l ^ 2) hq (PowerSeries.map τ f) := by
    simp only [frobOp, pow_one]; rw [PowerSeries.expand_apply]
  rw [hfrob] at hH
  have hid : ε⁻¹ • f - (l : K)⁻¹ • (PowerSeries.map τ (ε⁻¹ • f)).subst ((X : K⟦X⟧) ^ (l ^ 2)) =
      (ε⁻¹ * (l : K)⁻¹) • (C (l : K) * f - C c * PowerSeries.expand (l ^ 2) hq (PowerSeries.map τ f)) := by
    rw [← PowerSeries.expand_apply _ hq, PowerSeries.smul_eq_C_mul, map_mul, map_C, map_mul,
      PowerSeries.expand_C, hτ]
    ext n
    simp only [map_sub, coeff_smul, coeff_C_mul, smul_eq_mul]
    field_simp
  intro n
  rw [hid, coeff_smul, smul_eq_mul, norm_mul, norm_mul, norm_inv, norm_inv, hε, inv_one, one_mul]
  have hlp : 0 < ‖(l : K)‖ := norm_pos_iff.2 hl
  calc ‖(l : K)‖⁻¹ * _ ≤ ‖(l : K)‖⁻¹ * ‖(l : K)‖ := mul_le_mul_of_nonneg_left (hH n) (inv_nonneg.2 hlp.le)
    _ = 1 := inv_mul_cancel₀ hlp.ne'

theorem funEqType_of_unit {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K} {g : K⟦X⟧}
    (hg : Formalism.G.IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K)) :
    Formalism.G.IsFunEqType p q σ g := by
  have hx : (PowerSeries.map σ g).subst ((X : K⟦X⟧) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro n
  have := hg (Finsupp.single () n)
  rw [← hx] at this
  exact this

theorem honda_funEq : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), Formalism.L2.Th1.C.IsLogPair f e → ∀ c ε : K, ‖ε‖ = 1 → ε = c * (σ ^ 2) ε →
    CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f) →
    CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  intro K _ _ _ l σ hU f e hfe c ε hε hc hH
  have hS := setting hU
  have hl2 : 2 ≤ l := hU.2.1.le
  have hl : (l : K) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hq : l ^ 2 ≠ 0 := by positivity
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  obtain ⟨hf0, hf1, he0, hef, -⟩ := hfe
  have hg := funEq_scaled hε hc hH hl
  have hg0 : constantCoeff (ε⁻¹ • f) = 0 := by simp [hf0]
  have hαS : PowerSeries.HasSubst (ε • X : K⟦X⟧) := PowerSeries.HasSubst.smul_X' ε
  have hα0 : MvPowerSeries.constantCoeff (ε • X : K⟦X⟧) = 0 := by
    show constantCoeff (ε • X : K⟦X⟧) = 0
    simp
  have hαI : Formalism.G.IntegralMv (ε • X : K⟦X⟧) := by
    intro d
    rw [Finsupp.unique_single d]
    show ‖coeff (d ()) (ε • X : K⟦X⟧)‖ ≤ 1
    rw [coeff_smul, coeff_X, smul_eq_mul]
    split_ifs <;> simp [hε]
  have hMv := Formalism.LT.funEqSubst K l (l ^ 2) hq (σ ^ 2) hS (ε⁻¹ • f) hg0 hg Unit (ε • X : K⟦X⟧) hα0 hαI
  set ft : K⟦X⟧ := (ε⁻¹ • f).subst (ε • X : K⟦X⟧) with hft
  have hftE : Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) ft := funEqType_of_unit hq hMv
  have hftr : ft = ε⁻¹ • rescale ε f := by
    rw [hft, PowerSeries.subst_smul hαS, PowerSeries.rescale_eq_subst]
  have hft0 : constantCoeff ft = 0 := by
    rw [hftr, ← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hf0]
    simp
  have hft1 : coeff 1 ft = 1 := by
    rw [hftr, coeff_smul, coeff_rescale, hf1, smul_eq_mul]; field_simp
  have hL0 : constantCoeff (ltLog K l) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_ltLog_of_not
    rintro ⟨j, hj⟩
    exact (pow_ne_zero j hq) hj.symm
  have hLE : Formalism.G.IsFunEqType l (l ^ 2) (σ ^ 2) (ltLog K l) := by
    unfold Formalism.G.IsFunEqType
    rw [ltLog_funEq l hl2]
    intro n
    rw [coeff_X]; split_ifs <;> simp
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ ^ 2) hS ft (ltLog K l) hft0 hft1 hftE hL0 hLE
  have hhS : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hεh0 : constantCoeff (ε • h) = 0 := by simp [hh0]
  have hεhS : PowerSeries.HasSubst (ε • h) := PowerSeries.HasSubst.of_constantCoeff_zero' hεh0
  have hXh : (ε • X : K⟦X⟧).subst h = ε • h := by
    rw [PowerSeries.subst_smul hhS, PowerSeries.subst_X hhS]
  have hfεh : f.subst (ε • h) = ε • ltLog K l := by
    rw [← hh, hft, PowerSeries.subst_smul hαS, PowerSeries.subst_smul hhS,
      PowerSeries.subst_comp_subst_apply hαS hhS, hXh, smul_smul, mul_inv_cancel₀ hε0, one_smul]
  have hmain : e.subst (C ε * ltLog K l) = ε • h := by
    rw [← PowerSeries.smul_eq_C_mul, ← hfεh, ← PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf0) hεhS, hef, PowerSeries.subst_X hεhS]
  intro n
  rw [hmain, coeff_smul, smul_eq_mul, norm_mul, hε, one_mul]
  exact hhI n

end GlobalTheory.HondaFunEq
