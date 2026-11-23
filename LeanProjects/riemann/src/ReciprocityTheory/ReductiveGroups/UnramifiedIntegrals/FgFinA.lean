import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffOneSubstOfConstantCoeffEqZero
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.SemilinNormPowSubPow

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem FrobField.funEqSetting_sq [CompleteSpace K] (h : FrobField K l σ) :
    FunctionalEquationSetting K l (l ^ 2) (σ.comp σ) :=
  ⟨h.prime, ⟨2, two_pos, rfl⟩, h.norm_l, fun a ha => h.norm_sq_sub_pow_le a ha⟩

omit [IsUltrametricDist K] [CharZero K] in

theorem ltLog_sub_eq_X (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ (ltLog K l)).subst ((X : PowerSeries K) ^ (l ^ 2))
      = X := by
  have hq : 2 ≤ l ^ 2 := by nlinarith
  have hq0 : l ^ 2 ≠ 0 := by omega
  have hsub : ∀ (f : PowerSeries K) {k : ℕ} (_ : k ≠ 0) (m : ℕ),
      coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
    intro f k hk m
    have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
    rw [PowerSeries.coeff_subst' ha]
    simp only [← pow_mul, PowerSeries.coeff_X_pow]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [finsum_eq_single _ q]
      · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
      · intro d hd
        have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
        simp [this]
    · rw [finsum_eq_zero_of_forall_eq_zero]
      intro d
      have : m ≠ k * d := fun h => hd ⟨d, h⟩
      simp [this]
  have hpow : ∀ j, coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
    intro j
    have hex : ∃ i : ℕ, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
    rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dif_pos hex]
    have hf : Nat.find hex = j := (Nat.pow_right_injective hq (Nat.find_spec hex)).symm
    rw [hf]
  ext n
  rw [map_sub, PowerSeries.coeff_smul, hsub _ hq0, PowerSeries.coeff_X]
  by_cases hn : ∃ j, n = (l ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    rcases j with _ | j
    · have h1 : (l ^ 2) ^ 0 = 1 := pow_zero _
      have hnd : ¬ l ^ 2 ∣ (l ^ 2) ^ 0 := by
        rw [h1]
        intro h
        have := Nat.le_of_dvd one_pos h
        omega
      rw [if_neg hnd, hpow 0, h1, if_pos rfl]
      simp
    · have hd : l ^ 2 ∣ (l ^ 2) ^ (j + 1) := dvd_pow_self _ (Nat.succ_ne_zero j)
      have hdiv : (l ^ 2) ^ (j + 1) / l ^ 2 = (l ^ 2) ^ j := by
        rw [pow_succ (l ^ 2) j, Nat.mul_div_cancel _ (by omega)]
      have hne : (l ^ 2) ^ (j + 1) ≠ 1 := by
        have : l ^ 2 ≤ (l ^ 2) ^ (j + 1) := Nat.le_self_pow (Nat.succ_ne_zero j) _
        omega
      rw [if_pos hd, hdiv, PowerSeries.coeff_map, hpow, hpow,
        if_neg hne, map_inv₀, map_pow, map_natCast, pow_succ (l : K) j, mul_inv]
      ring
  · have h0 : coeff n (ltLog K l) = 0 := by rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dif_neg hn]
    have hX : n ≠ 1 := fun h => hn ⟨0, by rw [h, pow_zero]⟩
    rw [h0, if_neg hX]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      have hm : ¬ ∃ j, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj, pow_succ (l ^ 2) j, mul_comm]⟩
      rw [Nat.mul_div_cancel_left m (by omega), PowerSeries.coeff_map, Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk,
        dif_neg hm, map_zero]
      simp
    · simp

theorem ltLog_type (hl : 2 ≤ l) (τ : K →+* K) : IsFunEqType l (l ^ 2) τ (ltLog K l) := by
  unfold IsFunEqType
  rw [ltLog_sub_eq_X hl τ]
  exact integralPS_X

omit [IsUltrametricDist K] [CharZero K] in

theorem isFunEqType_of_mv {p q : ℕ} (hq : q ≠ 0) (τ : K →+* K) (f : PowerSeries K)
    (h : IsFunEqTypeMv (ι := Unit) p q hq τ f) : IsFunEqType p q τ f := by
  unfold IsFunEqType IsFunEqTypeMv at *
  have he : (PowerSeries.map τ f).subst ((X : PowerSeries K) ^ q)
      = MvPowerSeries.expand q hq (MvPowerSeries.map τ f) := by
    first
    | rfl
    | exact (MvPowerSeries.expand_eq_subst _ _ _).symm
    | (simp only [MvPowerSeries.expand, PowerSeries.subst]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; congr 1)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom, PowerSeries.subst]; congr 1)
  rw [he]
  unfold IntegralPS
  intro n
  first
  | exact h (Finsupp.single () n)
  | exact (by unfold IntegralMv at h; exact h (Finsupp.single () n))

omit [IsUltrametricDist K] [CharZero K] in
theorem inv_mul_inv_eq_of_eq_mul (c ε t x : K) (hc : c ≠ 0) (h : ε = c * t) :
    x⁻¹ * t⁻¹ = ε⁻¹ * (c / x) := by
  rw [h, mul_inv, div_eq_mul_inv]
  calc x⁻¹ * t⁻¹ = (c⁻¹ * c) * (t⁻¹ * x⁻¹) := by rw [inv_mul_cancel₀ hc, one_mul, mul_comm]
    _ = c⁻¹ * t⁻¹ * (c * x⁻¹) := by ring

theorem fin_integral [CompleteSpace K] (hF : FrobField K l σ) (ex lam : PowerSeries K)
    (hlam0 : constantCoeff lam = 0) (hlam1 : coeff 1 lam = 1) (hex0 : constantCoeff ex = 0)
    (hinv : ex.subst lam = X) (c ε : K) (hc : ‖c‖ = 1) (hε : ‖ε‖ = 1) (hcε : ε = c * σ (σ ε))
    (hT : IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    IntegralPS (ex.subst (C ε * ltLog K l)) := by
  have hl2 : 2 ≤ l := hF.prime.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hF.prime.ne_zero
  have hS := hF.funEqSetting_sq
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hτε0 : σ (σ ε) ≠ 0 := fun h => hε0 (by rw [hcε, h, mul_zero])
  have hXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) := PowerSeries.HasSubst.X_pow hq

  set f0 : PowerSeries K := ε⁻¹ • lam with hf0
  have hf00 : constantCoeff f0 = 0 := by
    rw [hf0, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
      coeff_zero_eq_constantCoeff_apply, hlam0, smul_zero]
  have hf0T : IsFunEqType l (l ^ 2) (σ.comp σ) f0 := by
    unfold IsFunEqType
    have e : f0 - (l : K)⁻¹ • (PowerSeries.map (σ.comp σ) f0).subst ((X : PowerSeries K) ^ (l ^ 2))
        = C ε⁻¹ * (lam - (c / (l : K)) •
          (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
      have e1 : PowerSeries.map (σ.comp σ) f0 = (σ (σ ε))⁻¹ • PowerSeries.map (σ.comp σ) lam := by
        ext n
        rw [hf0, coeff_map, PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_map, smul_eq_mul,
          smul_eq_mul, map_mul, map_inv₀]
        rfl
      rw [e1, PowerSeries.subst_smul hXq, smul_smul, ← smul_eq_C_mul, smul_sub, smul_smul, hf0]
      congr 2
      have hc0 : c ≠ 0 := fun h => by simp [h] at hc
      exact inv_mul_inv_eq_of_eq_mul c ε _ _ hc0 hcε
    rw [e]
    exact integralPS_mul (integralPS_C (by rw [norm_inv, hε, inv_one])) hT

  set α : PowerSeries K := C ε * X with hα
  have hα0 : constantCoeff α = 0 := by rw [hα, map_mul, constantCoeff_X, mul_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hαI : IntegralPS α := integralPS_mul (integralPS_C hε.le) integralPS_X
  set f1 : PowerSeries K := f0.subst α with hf1
  have hf1T : IsFunEqType l (l ^ 2) (σ.comp σ) f1 :=
    isFunEqType_of_mv hq _ _ (Formalism.LT.funEqSubst K l (l ^ 2) hq (σ.comp σ) hS f0 hf00 hf0T Unit α
      hα0 ((integralPS_iff_mv α).1 hαI))
  have hf1e : f1 = ε⁻¹ • PowerSeries.rescale ε lam := by
    rw [hf1, hf0, PowerSeries.subst_smul hαs, PowerSeries.rescale_eq_subst, hα, ← smul_eq_C_mul]
  have hf10 : constantCoeff f1 = 0 := by
    rw [hf1e, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul, coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, hlam0]; simp
  have hf11 : coeff 1 f1 = 1 := by
    rw [hf1e, PowerSeries.coeff_smul, coeff_rescale, hlam1, pow_one, mul_one, smul_eq_mul,
      inv_mul_cancel₀ hε0]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ.comp σ) hS f1 (ltLog K l) hf10 hf11
    hf1T (ltLog_const l hl2) (ltLog_type hl2 _)
  have hhs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hβ0 : constantCoeff (C ε * h) = 0 := by rw [map_mul, hh0, mul_zero]
  have hβs : PowerSeries.HasSubst (C ε * h) := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have hlams : PowerSeries.HasSubst lam := PowerSeries.HasSubst.of_constantCoeff_zero' hlam0
  have e2 : α.subst h = C ε * h := by
    rw [hα, PowerSeries.subst_mul hhs, PowerSeries.subst_X hhs, PowerSeries.subst_C]; rfl
  have e3 : lam.subst (C ε * h) = C ε * ltLog K l := by
    rw [← hh, hf1, PowerSeries.subst_comp_subst_apply hαs hhs, e2, hf0,
      PowerSeries.subst_smul hβs, smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hε0,
      map_one, one_mul]
  rw [← e3, ← PowerSeries.subst_comp_subst_apply hlams hβs, hinv, PowerSeries.subst_X hβs]
  exact integralPS_mul (integralPS_C hε.le) hhI

end ReciprocityTheory.ChartRestriction.L1
