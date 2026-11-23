import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Ev

variable {R : Type} [CommRing R]

def ev0 (F : MvPowerSeries (Fin 2) R) : PowerSeries R :=
  MvPowerSeries.subst ![(X : PowerSeries R), 0] F

theorem coeff_evalYZero (F : MvPowerSeries (Fin 2) R) (n : ℕ) :
    coeff n (ev0 F) = MvPowerSeries.coeff (Finsupp.single 0 n) F := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  have hc : ∀ f : PowerSeries R, MvPowerSeries.coeff (Finsupp.single () n) f = coeff n f := fun f => rfl
  have h := MvPowerSeries.coeff_subst ha F (Finsupp.single () n)
  unfold ev0
  rw [← hc, h, finsum_eq_single _ (Finsupp.single 0 n)]
  · rw [Finsupp.prod_single_index (by simp), hc]
    simp
  · intro d hd
    rw [hc, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    by_cases h1 : d 1 = 0
    · rw [h1, pow_zero, mul_one, coeff_X_pow, if_neg, smul_zero]
      intro h0
      apply hd
      ext i
      fin_cases i
      · simp [h0]
      · simp [h1]
    · rw [zero_pow h1, mul_zero, map_zero, smul_zero]

theorem evalYZero_add (F G : MvPowerSeries (Fin 2) R) : ev0 (F + G) = ev0 F + ev0 G := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  unfold ev0
  rw [MvPowerSeries.subst_add ha]

theorem evalYZero_mul (F G : MvPowerSeries (Fin 2) R) : ev0 (F * G) = ev0 F * ev0 G := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  unfold ev0
  rw [MvPowerSeries.subst_mul ha]

theorem evalYZero_subst (φ : PowerSeries R) {P : MvPowerSeries (Fin 2) R}
    (hP : MvPowerSeries.constantCoeff P = 0) : ev0 (φ.subst P) = φ.subst (ev0 P) := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  have hP' : MvPowerSeries.HasSubst (fun _ : Unit => P) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hP)
  unfold ev0
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply hP' ha φ

private theorem mvPowerSeries_coeff_subst_X_eq_ite_single {S : Type} [CommRing S] {ι : Type} [DecidableEq ι] (i : ι) (f : PowerSeries S)
    (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X i : MvPowerSeries ι S)) =
      if e = Finsupp.single i (e i) then coeff (e i) f else 0 := by
  have ha : HasSubst (MvPowerSeries.X i : MvPowerSeries ι S) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [PowerSeries.coeff_subst ha]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h]
    · intro d hd
      rw [if_neg]
      intro he
      exact hd (by rw [he, Finsupp.single_eq_same])
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro he
    exact h (by rw [he, Finsupp.single_eq_same])

theorem evalYZero_atX (φ : PowerSeries R) : ev0 (atX φ) = φ := by
  ext n
  rw [coeff_evalYZero]
  unfold atX
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single]
  simp

theorem evalYZero_atY (φ : PowerSeries R) : ev0 (atY φ) = C (constantCoeff φ) := by
  ext n
  rw [coeff_evalYZero, coeff_C]
  unfold atY
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (show ¬ n = 0 by omega), if_neg]
    intro h
    have h1 := congrArg (fun e => e 0) h
    simp at h1
    omega

end Ev

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}

theorem partialYAtZero_eq (F : MvPowerSeries (Fin 2) K) : d2 F = ev0 (MvPowerSeries.pderiv K 1 F) := by
  ext n
  rw [coeff_evalYZero, MvPowerSeries.coeff_pderiv]
  simp [d2]

theorem integralPS_partialYAtZero (hΦ : IntegralMv Φ) : IntegralPS (d2 Φ) := by
  unfold IntegralMv at hΦ
  unfold IntegralPS d2
  intro n
  rw [coeff_mk]
  exact hΦ _

theorem divBy_partialYAtZero {x : K} {F : MvPowerSeries (Fin 2) K} (hF : DivByMv x F) : DivBy x (d2 F) := by
  unfold DivByMv at hF
  unfold DivBy d2
  intro n
  rw [coeff_mk]
  exact hF _

theorem partialYAtZero_subst (D : PowerSeries K) {P : MvPowerSeries (Fin 2) K}
    (hP : MvPowerSeries.constantCoeff P = 0) :
    d2 (D.subst P) = (derivative K D).subst (ev0 P) * d2 P := by
  rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst hP, evalYZero_mul, evalYZero_subst _ hP, partialYAtZero_eq]

theorem partialYAtZero_atX (D : PowerSeries K) : d2 (atX D) = 0 := by
  ext n
  unfold d2 atX
  rw [coeff_mk, mvPowerSeries_coeff_subst_X_eq_ite_single, if_neg, map_zero]
  intro h
  have h1 := congrArg (fun e => e 1) h
  simp at h1

theorem partialYAtZero_atY (D : PowerSeries K) : d2 (atY D) = C (coeff 1 D) := by
  ext n
  unfold d2 atY
  rw [coeff_mk, mvPowerSeries_coeff_subst_X_eq_ite_single, coeff_C]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (show ¬ n = 0 by omega), if_neg]
    intro h
    have h1 := congrArg (fun e => e 0) h
    simp at h1
    omega

theorem partialYAtZero_sub (F G : MvPowerSeries (Fin 2) K) : d2 (F - G) = d2 F - d2 G := by
  ext n
  simp only [d2, PowerSeries.coeff_mk, map_sub]

theorem partialYAtZero_add (F G : MvPowerSeries (Fin 2) K) : d2 (F + G) = d2 F + d2 G := by
  ext n
  simp only [d2, PowerSeries.coeff_mk, map_add]

theorem LawD.evalYZero_eq (h : LawD lam Φ) : ev0 Φ = X := by
  have hc : constantCoeff (ev0 Φ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_evalYZero, Finsupp.single_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h.Φ0
  have h1 := congrArg ev0 h.log
  rw [evalYZero_subst lam h.Φ0, evalYZero_add, evalYZero_atX, evalYZero_atY, h.lam0, map_zero, add_zero] at h1
  have hu : IsUnit (coeff 1 lam) := by rw [h.lam1]; exact isUnit_one
  have hl : HasSubst lam := HasSubst.of_constantCoeff_zero h.lam0
  have he : HasSubst (ev0 Φ) := HasSubst.of_constantCoeff_zero hc
  have h2 := PowerSeries.subst_comp_subst_apply hl he (lam.substInvOfIsUnit hu)
  rw [PowerSeries.subst_substInvOfIsUnit_left lam h.lam0 hu, PowerSeries.subst_X he, h1,
    PowerSeries.subst_substInvOfIsUnit_left lam h.lam0 hu] at h2
  exact h2

private theorem powerSeries_subst_X_self_commRing {S : Type} [CommRing S] (t : PowerSeries S) :
    t.subst (X : PowerSeries S) = t := by
  ext n
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero constantCoeff_X), finsum_eq_single _ n]
  · simp
  · intro d hd
    simp [coeff_X_pow, Ne.symm hd]

theorem LawD.coeffY_subst (h : LawD lam Φ) (D : PowerSeries K) :
    d2 (D.subst Φ) = derivative K D * d2 Φ := by
  rw [partialYAtZero_subst D h.Φ0, h.evalYZero_eq, powerSeries_subst_X_self_commRing]

theorem LawD.deriv_mul (h : LawD lam Φ) : derivative K lam * d2 Φ = 1 := by
  have h1 := congrArg d2 h.log
  rw [h.coeffY_subst, partialYAtZero_add, partialYAtZero_atX, partialYAtZero_atY, h.lam1, zero_add, map_one] at h1
  exact h1

theorem LawD.deriv_const (h : LawD lam Φ) : constantCoeff (derivative K lam) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
  simp [h.lam1]

theorem LawD.constantCoeff_partialYAtZero (h : LawD lam Φ) : constantCoeff (d2 Φ) = 1 := by
  have h1 := congrArg constantCoeff h.deriv_mul
  rw [map_mul, h.deriv_const, one_mul, map_one] at h1
  exact h1

theorem LawD.deriv_integral (h : LawD lam Φ) : IntegralPS (derivative K lam) := by
  have hm := h.deriv_mul
  have ha := integralPS_partialYAtZero h.Φint
  have h0 := h.constantCoeff_partialYAtZero
  unfold IntegralPS at ha ⊢
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h.deriv_const]
    · have hc := congrArg (coeff n) hm
      simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
        Nat.sub_self, coeff_zero_eq_constantCoeff_apply, h0, mul_one, coeff_one,
        if_neg (show n ≠ 0 by omega)] at hc
      have e : coeff n (derivative K lam) =
          -∑ k ∈ Finset.range n, coeff k (derivative K lam) * coeff (n - k) (d2 Φ) := by
        linear_combination hc
      rw [e, norm_neg]
      refine Finset.sum_induction _ (fun x => ‖x‖ ≤ 1)
        (fun x y hx hy => (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy))
        (by simp) fun k hk => ?_
      rw [norm_mul]
      have hk' := Finset.mem_range.mp hk
      calc ‖coeff k (derivative K lam)‖ * ‖coeff (n - k) (d2 Φ)‖ ≤ 1 * 1 :=
            mul_le_mul (ih k hk') (ha _) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

theorem hon_deriv (h : LawD lam Φ) (x : K) (D : PowerSeries K)
    (hadd : DivByMv x (D.subst Φ - atX D - atY D)) :
    DivBy x (derivative K D - C (coeff 1 D) * derivative K lam) := by
  have h1 := divBy_partialYAtZero hadd
  rw [partialYAtZero_sub, partialYAtZero_sub, h.coeffY_subst, partialYAtZero_atX, partialYAtZero_atY, sub_zero] at h1
  have e : derivative K D - C (coeff 1 D) * derivative K lam =
      derivative K lam * (derivative K D * d2 Φ - C (coeff 1 D)) := by
    linear_combination (-derivative K D) * h.deriv_mul
  rw [e]
  have hl := h.deriv_integral
  unfold DivBy at h1 ⊢
  unfold IntegralPS at hl
  intro n
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖x‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by simp) fun p _ => ?_
  rw [norm_mul]
  calc ‖coeff p.1 (derivative K lam)‖ * ‖coeff p.2 (derivative K D * d2 Φ - C (coeff 1 D))‖
        ≤ 1 * ‖x‖ := mul_le_mul (hl _) (h1 _) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _

end ReciprocityTheory.ChartRestriction.L1
