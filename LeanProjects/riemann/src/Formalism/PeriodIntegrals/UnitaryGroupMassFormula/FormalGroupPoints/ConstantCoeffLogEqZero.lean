import Formalism.PeriodIntegrals.FglPtW

noncomputable section

namespace PI.UnitaryGroupMassFormula.FglPtW

open PI.FglPtW

theorem constantCoeff_log_eq_zero {K : Type} [CommRing K] {l ex : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ex = 0) (hlex : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have h := congrArg MvPowerSeries.constantCoeff hlex
  rw [PowerSeries.constantCoeff_subst hex, finsum_eq_single _ 0] at h
  · have h' := h.trans PowerSeries.constantCoeff_X
    simpa using h'
  · intro d hd
    have : MvPowerSeries.constantCoeff (ex ^ d) = 0 := by
      rw [map_pow]
      have h0' : MvPowerSeries.constantCoeff ex = 0 := h0
      rw [h0', zero_pow hd]
    rw [this, smul_zero]

theorem log_exp_eq {K : Type} [CommRing K] {l ex : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ex = 0) (hlex : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type} (y : MvPowerSeries σ K) (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy', hlex, PowerSeries.subst_X hy']

theorem linGen_of (hA : AddGen) (hM : MulGen) : LinGen := by
  intro K _ S l ex h0 hlex hF ι _ c hc σ a ha
  classical
  have hl0 := constantCoeff_log_eq_zero h0 hlex
  have cc : ∀ y : MvPowerSeries σ K, MvPowerSeries.constantCoeff y = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst y l) = 0 :=
    fun y hy => PowerSeries.constantCoeff_subst_eq_zero hy l hl0
  have csum : ∀ s : Finset ι, MvPowerSeries.constantCoeff
      (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) = 0 := by
    intro s
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_mul, cc _ (ha j).2, mul_zero]
  suffices H : ∀ s : Finset ι, PtOver S (PowerSeries.subst
      (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) ex) from H Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, PowerSeries.subst_zero_of_constantCoeff_zero h0]
    exact ⟨fun n => by simp [S.zero_mem], by simp⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have hx : MvPowerSeries.constantCoeff
        (MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) = 0 := by
      rw [map_mul, cc _ (ha j).2, mul_zero]
    have key : PowerSeries.subst (MvPowerSeries.C (c j) * PowerSeries.subst (a j) l +
          ∑ i ∈ s, MvPowerSeries.C (c i) * PowerSeries.subst (a i) l) ex =
        PowerSeries.subst
          (PowerSeries.subst (PowerSeries.subst
            (MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) ex) l +
           PowerSeries.subst (PowerSeries.subst
            (∑ i ∈ s, MvPowerSeries.C (c i) * PowerSeries.subst (a i) l) ex) l) ex := by
      rw [log_exp_eq h0 hlex _ hx, log_exp_eq h0 hlex _ (csum s)]
    rw [key]
    exact hA K S l ex h0 hlex hF σ _ _ (hM K S l ex h0 hlex (c j) (hc j) σ (a j) (ha j)) ih

end PI.UnitaryGroupMassFormula.FglPtW

end
