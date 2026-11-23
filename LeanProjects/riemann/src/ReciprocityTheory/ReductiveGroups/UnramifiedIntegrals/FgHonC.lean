import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonA
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem desc_const (D : PowerSeries K) : constantCoeff (desc l D) = constantCoeff D := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    desc, PowerSeries.coeff_mk, mul_zero]

theorem desc_integral {D : PowerSeries K} (hD : IntegralPS D) : IntegralPS (desc l D) := by
  unfold IntegralPS at hD ⊢
  intro n
  rw [desc, PowerSeries.coeff_mk]
  exact hD _

theorem coeff_one_desc (D : PowerSeries K) : coeff 1 (desc l D) = coeff l D := by
  rw [desc, PowerSeries.coeff_mk, mul_one]

private theorem coeff_subst_X_pow_lemma (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
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

theorem desc_congr (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (D : PowerSeries K)
    (hD : DivBy (l : K) (derivative K D)) :
    DivBy (l : K) (D - (desc l D).subst ((X : PowerSeries K) ^ l)) ∧
      IntegralPS (derivative K (desc l D)) := by
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hD' : ∀ n, ‖coeff n (derivative K D)‖ ≤ ‖(l : K)‖ := hD
  have hD2 : ∀ m, ‖coeff (m + 1) D‖ * ‖((m : K) + 1)‖ ≤ ‖(l : K)‖ := by
    intro m
    have h := hD' m
    rwa [PowerSeries.coeff_derivative, norm_mul] at h
  refine ⟨?_, ?_⟩
  · intro m
    rw [map_sub, coeff_subst_X_pow_lemma _ hl.ne_zero]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [desc, PowerSeries.coeff_mk, Nat.mul_div_cancel_left q hl.pos, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [sub_zero]
      have hm0 : m ≠ 0 := fun h => hd (h ▸ dvd_zero l)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h1 := hD2 m'
      have hu : ‖((m' : K) + 1)‖ = 1 := by
        have h2 := norm_natCast_of_coprime hl hl1 (m' + 1) hd
        push_cast at h2
        exact h2
      rwa [hu, mul_one] at h1
  · intro m
    rw [PowerSeries.coeff_derivative, desc, PowerSeries.coeff_mk, norm_mul]
    have e : l * (m + 1) - 1 + 1 = l * (m + 1) :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hl.ne_zero (Nat.succ_ne_zero m)))
    have e2 : ((l * (m + 1) - 1 : ℕ) : K) + 1 = (l : K) * ((m : K) + 1) := by
      rw [← Nat.cast_add_one, e]
      push_cast
      ring
    have h1 := hD2 (l * (m + 1) - 1)
    rw [e2, e, norm_mul] at h1
    have h2 : ‖(l : K)‖ * (‖coeff (l * (m + 1)) D‖ * ‖((m : K) + 1)‖) ≤ ‖(l : K)‖ * 1 := by
      linarith [h1]
    exact le_of_mul_le_mul_left h2 hlpos

theorem desc_key {ι : Type} (hF : FrobField K l σ) {D : PowerSeries K}
    (hD0 : constantCoeff D = 0) (hD' : DivBy (l : K) (derivative K D)) (P : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) (MvPowerSeries.expand l hF.prime.ne_zero
      ((desc l D).subst (MvPowerSeries.map σ P)) - D.subst P) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  obtain ⟨h1, h2⟩ := desc_congr hF.prime hF.norm_l D hD'
  have hσP0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero hσP0)]
  have hfc := FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
  have hE0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) = 0 := by
    rw [MvPowerSeries.constantCoeff_expand, hσP0]
  have hEi : IntegralMv (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) := by
    rw [integralMv_iff_divBy_one, divByMv_expand_iff, ← integralMv_iff_divBy_one]
    exact hF.integralMv_map hP
  have hPl0 : MvPowerSeries.constantCoeff (P ^ l) = 0 := by
    rw [map_pow, hP0, zero_pow hl0]
  have h3 := qls hF.prime hF.norm_l (desc l D) (by rw [desc_const, hD0]) h2
    (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) (P ^ l) hE0 hPl0 hEi
    (integralMv_pow hP l) (by
      have := divByMv_neg hfc
      rwa [neg_sub] at this)
  have h4 : (desc l D).subst (P ^ l) =
      PowerSeries.subst P ((desc l D).subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have h5 := divByMv_subst h1 hP0 hP
  rw [PowerSeries.subst_sub hPs, ← h4] at h5
  have := divByMv_sub h3 h5
  rwa [sub_sub_sub_cancel_right] at this

theorem desc_QCls (hF : FrobField K l σ) {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {b : K}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (hΦ : IntegralMv Φ) (hA0 : constantCoeff A = 0)
    (hA : IntegralPS A) (hb : ‖b‖ ≤ 1) {D : PowerSeries K} (hD : QCls l Φ A b D)
    (hD' : DivBy (l : K) (derivative K D)) :
    QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) b (desc l D) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  refine ⟨by rw [desc_const, hD.D0], (desc_congr hF.prime hF.norm_l D hD').2, ?_, ?_⟩
  · rw [← divByMv_expand_iff _ l hl0, map_sub, map_sub]
    have h1 := desc_key hF hD.D0 hD' Φ hΦ0 hΦ
    have h2 := desc_key hF hD.D0 hD' (MvPowerSeries.X (0 : Fin 2)) (by simp) (integralMv_X _)
    have h3 := desc_key hF hD.D0 hD' (MvPowerSeries.X (1 : Fin 2)) (by simp) (integralMv_X _)
    rw [MvPowerSeries.map_X] at h2 h3
    have h4 := divByMv_add (divByMv_sub (divByMv_sub h1 h2) h3) hD.add
    convert h4 using 1
    simp only [atX, atY]
    ring
  · rw [divBy_iff_mv, ← divByMv_expand_iff _ l hl0, map_sub, map_mul]
    have h1 := desc_key hF hD.D0 hD' (ι := Unit) A hA0 ((integralPS_iff_mv A).1 hA)
    have h2 := desc_key hF hD.D0 hD' (ι := Unit) (X : PowerSeries K) (by simp [PowerSeries.X])
      ((integralPS_iff_mv _).1 integralPS_X)
    rw [show MvPowerSeries.map σ (X : PowerSeries K) = (X : PowerSeries K) from PowerSeries.map_X σ,
      PowerSeries.X_subst, PowerSeries.X_subst] at h2
    have h3 := divByMv_mul_left ((integralPS_iff_mv _).1 (integralPS_C hb)) h2
    have h4 := divByMv_add (divByMv_sub h1 h3) ((divBy_iff_mv _ _).1 hD.eig)
    have hC : MvPowerSeries.expand l hl0 (C b : PowerSeries K) = (C b : PowerSeries K) :=
      PowerSeries.expand_C l hl0 b
    rw [hC]
    convert h4 using 1
    simp only [PowerSeries.map]
    ring

end ReciprocityTheory.ChartRestriction.L1
