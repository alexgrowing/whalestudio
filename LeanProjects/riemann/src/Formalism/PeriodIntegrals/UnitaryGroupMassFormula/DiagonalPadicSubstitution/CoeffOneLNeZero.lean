import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOps

noncomputable section

open Classical

namespace PI.BeDiagZp.IdentW

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_l {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have hex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key := congrArg (PowerSeries.coeff 0) h
  rw [PowerSeries.coeff_subst' hex, finsum_eq_single _ 0] at key
  · simpa using key
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hex0, zero_pow hd, smul_zero]

theorem coeff_one_l_ne_zero {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 l ≠ 0 := by
  intro h1
  have hex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hXe : (PowerSeries.X : PowerSeries ℂ_[p]) ∣ ex := PowerSeries.X_dvd_iff.2 hex0
  have key := congrArg (PowerSeries.coeff 1) h
  rw [PowerSeries.coeff_subst' hex, finsum_eq_zero_of_forall_eq_zero] at key
  · simp at key
  · intro d
    rcases Nat.lt_or_ge d 2 with hd | hd
    · interval_cases d
      · simp
      · rw [h1, zero_smul]
    · have h0 : PowerSeries.coeff 1 (ex ^ d) = 0 :=
        PowerSeries.X_pow_dvd_iff.1 ((pow_dvd_pow PowerSeries.X hd).trans (pow_dvd_pow_of_dvd hXe d)) 1
          (by norm_num)
      rw [h0, smul_zero]

theorem subst_left_inv {K : Type*} [Field K] {l ex : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hu : IsUnit (PowerSeries.coeff 1 l)) (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  set Q := PowerSeries.substInvOfIsUnit l hu with hQ
  have hQl : PowerSeries.subst l Q = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left l hl0 hu
  have hl : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key : PowerSeries.subst ex (PowerSeries.subst l Q) = PowerSeries.subst (PowerSeries.subst ex l) Q :=
    PowerSeries.subst_comp_subst_apply hl hex Q
  rw [hQl, h, PowerSeries.subst_X hex, PowerSeries.X_subst] at key
  rw [key, hQl]

theorem subst_l_ex {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X :=
  subst_left_inv (constantCoeff_l hex0 h) (isUnit_iff_ne_zero.2 (coeff_one_l_ne_zero hex0 h)) hex0 h

theorem l_ex_apply {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) (y : MvPowerSeries σ ℂ_[p])
    (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hy' := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy' l, h, PowerSeries.subst_X hy']

theorem ex_l_apply {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) (y : MvPowerSeries σ ℂ_[p])
    (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y l) ex = y := by
  have hl := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_l hex0 h)
  have hy' := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hl hy' ex, subst_l_ex hex0 h, PowerSeries.subst_X hy']

theorem ident_holds : Ident := by
  intro p _ l ex hex0 h
  have hl0 := constantCoeff_l hex0 h
  refine ⟨hl0, fun σ a b ha hb => ?_⟩
  have hla : MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero ha l hl0
  have hlb : MvPowerSeries.constantCoeff (PowerSeries.subst b l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hb l hl0
  have hCa : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (MvPowerSeries.C c * PowerSeries.subst a l) = 0 :=
    fun c => by rw [map_mul, hla, mul_zero]
  have lmul : ∀ c : ℂ_[p], PowerSeries.subst (mulBy l ex c a) l = MvPowerSeries.C c * PowerSeries.subst a l :=
    fun c => l_ex_apply hex0 h _ (hCa c)
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hla, hlb, add_zero]) ex hex0,
    fun c => PowerSeries.constantCoeff_subst_eq_zero (hCa c) ex hex0, ?_, ?_, fun c d => ?_, fun c => ?_, ?_, ?_⟩
  · unfold add; rw [add_comm]
  · unfold add mulBy; rw [map_ofNat, two_mul]
  · unfold add; rw [lmul, lmul, ← add_mul, ← map_add]; rfl
  · unfold add; rw [lmul]; unfold mulBy; rw [map_add, map_one, add_mul, one_mul]
  · unfold mulBy; rw [map_one, one_mul]; exact ex_l_apply hex0 h a ha
  · unfold mulBy; rw [map_zero, zero_mul]; exact PowerSeries.subst_zero_of_constantCoeff_zero hex0

end PI.BeDiagZp.IdentW
