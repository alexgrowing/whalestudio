import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Development

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit

theorem compositionalInverseSymm : S1 := by
  intro K _ l ex hex hinv
  have hsub : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have hsplit : l = PowerSeries.C (PowerSeries.constantCoeff l) +
        (l - PowerSeries.C (PowerSeries.constantCoeff l)) := by ring
    have h0 : MvPowerSeries.constantCoeff
        (PowerSeries.subst ex (l - PowerSeries.C (PowerSeries.constantCoeff l))) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hex _ (by simp)
    have key : MvPowerSeries.constantCoeff (PowerSeries.subst ex l) = PowerSeries.constantCoeff l := by
      conv_lhs => rw [hsplit]
      rw [PowerSeries.subst_add hsub, map_add, h0, PowerSeries.subst_C]
      simp
    rw [hinv] at key
    rw [← key]
    exact PowerSeries.constantCoeff_X
  have hu : IsUnit (PowerSeries.coeff 1 ex) := by
    refine Ne.isUnit fun h1 => ?_
    have h2 : (2 : ℕ∞) ≤ ex.order := by
      refine PowerSeries.le_order ex 2 fun i hi => ?_
      have hi' : i < 2 := by exact_mod_cast hi
      interval_cases i
      · simpa using hex
      · exact h1
    have h3 := PowerSeries.le_order_subst_right' (φ := l) hex hl0
    rw [hinv, PowerSeries.order_X] at h3
    have := h2.trans h3
    norm_num at this
  have hQ := PowerSeries.HasSubst.substInvOfIsUnit ex hu
  have hexQ := PowerSeries.subst_substInvOfIsUnit_right ex hex hu
  have hlQ : l = PowerSeries.substInvOfIsUnit ex hu := by
    calc l = PowerSeries.subst (PowerSeries.X : PowerSeries K) l := (PowerSeries.X_subst l).symm
      _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.substInvOfIsUnit ex hu) ex) l := by
          rw [hexQ]
      _ = PowerSeries.subst (PowerSeries.substInvOfIsUnit ex hu) (PowerSeries.subst ex l) :=
          (PowerSeries.subst_comp_subst_apply hsub hQ l).symm
      _ = PowerSeries.subst (PowerSeries.substInvOfIsUnit ex hu) (PowerSeries.X : PowerSeries K) := by
          rw [hinv]
      _ = PowerSeries.substInvOfIsUnit ex hu := PowerSeries.subst_X hQ
  refine ⟨hl0, ?_⟩
  rw [hlQ]
  exact hexQ

variable {K : Type} [Field K]

theorem subst_zero_of {τ : Type} (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries τ K) f = 0 := by
  rw [PowerSeries.subst_zero_eq_C_constantCoeff, hf]
  simp

theorem pt_lg (g : Dat K) {τ : Type} (hl0 : PowerSeries.constantCoeff g.l = 0)
    (hinv : PowerSeries.subst g.l g.ex = PowerSeries.X) {y : MvPowerSeries τ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : g.pt (g.lg y) = y := by
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  simp only [Dat.pt, Dat.lg]
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0) hy', hinv,
    PowerSeries.subst_X (R := K) hy']

theorem be_mulBy_zero (g : Dat K) {τ : Type} (hex0 : PowerSeries.constantCoeff g.ex = 0)
    (hph0 : PowerSeries.constantCoeff g.ph = 0) (hl0 : PowerSeries.constantCoeff g.l = 0)
    (hinv : PowerSeries.subst g.l g.ex = PowerSeries.X) (x : MvPowerSeries τ K)
    {y : MvPowerSeries τ K} (hy : MvPowerSeries.constantCoeff y = 0) :
    g.be (g.mulBy 0 x) y = 0 := by
  have hm : g.mulBy 0 x = 0 := by
    simp only [Dat.mulBy, map_zero, zero_mul, Dat.pt]
    exact subst_zero_of g.ex hex0
  have hlg0 : g.lg (0 : MvPowerSeries τ K) = 0 := subst_zero_of g.l hl0
  have hadd : g.add 0 y = y := by
    simp only [Dat.add, hlg0, zero_add]
    exact pt_lg g hl0 hinv hy
  have hph : g.phAt (0 : MvPowerSeries τ K) = 0 := subst_zero_of g.ph hph0
  simp only [Dat.be, hm, hadd, hph, sub_zero, sub_self]

theorem orthogonalSplitPolarizationVanishes : S2 := by
  intro K _ g hex hinv0 hph κ ι ι' _ _ _ a a' ha
  obtain ⟨hl0, hinv⟩ := compositionalInverseSymm K g.l g.ex hex hinv0
  simp only [Dat.sdR]
  refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun f' _ => ?_
  simp only [ha f f', Prod.fst_zero]
  exact be_mulBy_zero g hex hph hl0 hinv _ (by simp)

end PI.FglPhSplit.Wk

end
