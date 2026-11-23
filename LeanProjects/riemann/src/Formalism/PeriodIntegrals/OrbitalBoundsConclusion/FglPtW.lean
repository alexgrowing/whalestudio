import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.AddGenThm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.MulGenThm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.ConstantCoeffLogEqZero

theorem formal_group_add_generation : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm

theorem formal_group_mul_generation : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm

private theorem cc_subst_lemma {K : Type*} [CommRing K] {σ : Type*} {a : MvPowerSeries σ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, ha, zero_pow hd]

private theorem powerSeries_subst_zero_of_constantCoeff_eq_zero' {K : Type*} [CommRing K] {σ : Type*} {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.subst (0 : MvPowerSeries σ K) f = 0 := by
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  rw [finsum_eq_single _ 0]
  · simp [hf]
  · intro d hd
    simp [zero_pow hd]

private theorem subst_subst_eq_of_subst_eq_X {K : Type*} [CommRing K] {l ex : PowerSeries K}
    (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type*} {u : MvPowerSeries σ K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst (PowerSeries.subst u ex) l = u := by
  have hexS : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have huS : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [← PowerSeries.subst_comp_subst_apply hexS huS, hl, PowerSeries.subst_X huS]

theorem formal_group_lin_generation : PI.FglPtW.LinGen := by
  intro K _ S l ex hex hl hadd ι _ c hc σ a ha
  classical
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := cc_subst_lemma (σ := Unit) (a := ex) hex l
    rw [hl] at h
    exact h.symm.trans PowerSeries.constantCoeff_X
  have hcc : ∀ j, MvPowerSeries.constantCoeff (MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) = 0 := by
    intro j
    rw [map_mul, cc_subst_lemma (ha j).2, hl0, mul_zero]
  have key : ∀ s : Finset ι, PI.FglPtW.PtOver S (PowerSeries.subst
      (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) ex) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, powerSeries_subst_zero_of_constantCoeff_eq_zero' hex]
      exact ⟨fun n => by simp [S.zero_mem], by simp⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hw : MvPowerSeries.constantCoeff
          (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero fun j _ => hcc j
      have hy := PI.FglPtW.Wk.mulGen_thm K S l ex hex hl (c i) (hc i) σ (a i) (ha i)
      have h := PI.FglPtW.Wk.addGen_thm K S l ex hex hl hadd σ _ _ hy ih
      rwa [subst_subst_eq_of_subst_eq_X hex hl (hcc i), subst_subst_eq_of_subst_eq_X hex hl hw] at h
  exact key Finset.univ
