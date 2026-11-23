import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonC

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Tools

variable {R : Type} [CommRing R]

theorem constCoeff_subst_zero {g s : PowerSeries R} (hs : constantCoeff s = 0) :
    constantCoeff (g.subst s) = constantCoeff g := by
  have ha : HasSubst s := HasSubst.of_constantCoeff_zero hs
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, hs, zero_pow hd]

theorem coeffOne_subst_zero {f s : PowerSeries R} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  have ha : HasSubst s := HasSubst.of_constantCoeff_zero hs
  have hX : X ∣ s := X_dvd_iff.mpr hs
  rw [PowerSeries.coeff_subst' ha, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ s ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]

theorem subst_C_mul_mv {ι : Type} {P : MvPowerSeries ι R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = MvPowerSeries.C c * f.subst P := by
  rw [← smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

theorem subst_C_mul_ps {P : PowerSeries R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = C c * f.subst P := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

end Tools

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.map (hF : FrobField K l σ) (h : LawD lam Φ) :
    LawD (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.lam0,
      map_zero]
  · rw [coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · have h1 := h.Φint
    unfold IntegralMv at h1 ⊢
    intro e
    rw [MvPowerSeries.coeff_map, hF.isom]
    exact h1 e
  · have h1 := congrArg (MvPowerSeries.map σ) h.log
    unfold atX atY at h1 ⊢
    rw [map_add] at h1
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.Φ0),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)),
      MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
    exact h1

theorem HD.map (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) (σ a) := by
  refine ⟨h.toLawD.map hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.A0,
      map_zero]
  · have h1 := h.Aint
    unfold IntegralPS at h1 ⊢
    intro n
    rw [coeff_map, hF.isom]
    exact h1 n
  · have h1 := congrArg (PowerSeries.map σ) h.Alog
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.A0)] at h1
    rw [map_mul, map_C] at h1
    exact h1
  · rw [h.a_sq, norm_sub_rev]
    exact h.a_ne
  · rw [h.a_sq]

theorem HD.coeff_one_A (h : HD σ lam Φ A a) : coeff 1 A = a := by
  have h1 := congrArg (coeff 1) h.Alog
  rw [coeffOne_subst_zero h.A0, coeff_C_mul, h.lam1, one_mul, mul_one] at h1
  exact h1

theorem HD.norm_a (h : HD σ lam Φ A a) : ‖a‖ ≤ 1 := by
  have h1 := h.Aint
  unfold IntegralPS at h1
  rw [← h.coeff_one_A]
  exact h1 1

theorem HD.qcls_lam (h : HD σ lam Φ A a) : QCls l Φ A a lam := by
  refine ⟨h.lam0, h.toLawD.deriv_integral, ?_, ?_⟩
  · have h0 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]; ring
    rw [h0]
    unfold DivByMv
    intro e
    simp
  · have h0 : lam.subst A - C a * lam = 0 := by rw [h.Alog]; ring
    rw [h0]
    unfold DivBy
    intro n
    simp

theorem eigen_trick {A : PowerSeries K} {b : K} (hA0 : constantCoeff A = 0) (D : PowerSeries K)
    (hD0 : constantCoeff D = 0) (h : DivBy (l : K) (D.subst A - C b * D))
    (hb : ‖coeff 1 A - b‖ = 1) : ‖coeff 1 D‖ ≤ ‖(l : K)‖ := by
  have h0 := h
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 D * coeff 1 A - b * coeff 1 D = coeff 1 D * (coeff 1 A - b) := by ring
  rw [map_sub, coeffOne_subst_zero hA0, coeff_C_mul, e, norm_mul, hb, mul_one] at h1
  exact h1

theorem divBy_C_mul {x c : K} (hc : ‖c‖ ≤ 1) {f : PowerSeries K} (hf : DivBy x f) :
    DivBy x (C c * f) := by
  unfold DivBy at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ 1 * ‖x‖ := mul_le_mul hc (hf n) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _

theorem divBy_C_mul' {x c : K} (hc : ‖c‖ ≤ ‖x‖) {f : PowerSeries K} (hf : IntegralPS f) :
    DivBy x (C c * f) := by
  unfold DivBy IntegralPS at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ ‖x‖ * 1 := mul_le_mul hc (hf n) (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _

theorem derivative_C_mul' (c : K) (f : PowerSeries K) :
    derivative K (C c * f) = C c * derivative K f := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul]

theorem QCls.norm_coeff_one {b : K} {D : PowerSeries K} (hD : QCls l Φ A b D) :
    ‖coeff 1 D‖ ≤ 1 := by
  have h0 := hD.dInt
  unfold IntegralPS at h0
  have h1 := h0 0
  rw [coeff_derivative] at h1
  simpa using h1

theorem HD.qcls_sub (h : HD σ lam Φ A a) {D : PowerSeries K} (hD : QCls l Φ A a D) :
    QCls l Φ A a (D - C (coeff 1 D) * lam) := by
  set c := coeff 1 D with hc
  have hc1 : ‖c‖ ≤ 1 := hD.norm_coeff_one
  have hΦ : HasSubst Φ := HasSubst.of_constantCoeff_zero h.Φ0
  have hA : HasSubst A := HasSubst.of_constantCoeff_zero h.A0
  have hX0 : HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)
  have hX1 : HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)
  have sub_subst : ∀ {P : MvPowerSeries (Fin 2) K} (_ : HasSubst P) (f g : PowerSeries K),
      (f - g).subst P = f.subst P - g.subst P := fun hP f g => by
    rw [← coe_substAlgHom hP, map_sub]
  have sub_substA : (D - C c * lam).subst A = D.subst A - C c * lam.subst A := by
    rw [← coe_substAlgHom hA, map_sub, coe_substAlgHom hA, subst_C_mul_ps hA]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hD.D0, h.lam0]
  · have hd := hD.dInt
    have hl := h.toLawD.deriv_integral
    unfold IntegralPS at hd hl ⊢
    intro n
    rw [map_sub, derivative_C_mul', map_sub, coeff_C_mul, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd n) ?_)
    rw [norm_neg, norm_mul]
    calc ‖c‖ * ‖coeff n (derivative K lam)‖ ≤ 1 * 1 :=
          mul_le_mul hc1 (hl n) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have e : (D - C c * lam).subst Φ - atX (D - C c * lam) - atY (D - C c * lam) =
        (D.subst Φ - atX D - atY D) - MvPowerSeries.C c * (lam.subst Φ - atX lam - atY lam) := by
      unfold atX atY
      rw [sub_subst hΦ, sub_subst hX0, sub_subst hX1, subst_C_mul_mv hΦ, subst_C_mul_mv hX0,
        subst_C_mul_mv hX1]
      ring
    have e2 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]; ring
    rw [e, e2, mul_zero, sub_zero]
    exact hD.add
  · have e : (D - C c * lam).subst A - C a * (D - C c * lam) = D.subst A - C a * D := by
      rw [sub_substA, h.Alog]
      ring
    rw [e]
    exact hD.eig

theorem lemmaQ (hF : FrobField K l σ) (h : HD σ lam Φ A a) {D : PowerSeries K}
    (hD : QCls l Φ A a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * lam - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  set E : PowerSeries K := D - C (coeff 1 D) * lam with hE
  have hEq : QCls l Φ A a E := h.qcls_sub hD
  have hE' : DivBy (l : K) (derivative K E) := by
    have := hon_deriv h.toLawD (l : K) D hD.add
    rwa [hE, map_sub, derivative_C_mul']
  have h1 : QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) a (desc l E) :=
    desc_QCls hF h.Φ0 h.Φint h.A0 h.Aint h.norm_a hEq hE'
  have c1 := (desc_congr hF.prime hF.norm_l E hE').1
  have hσ := h.map hF
  have hs : ‖coeff 1 (desc l E)‖ ≤ ‖(l : K)‖ :=
    eigen_trick hσ.A0 _ h1.D0 h1.eig (by rw [hσ.coeff_one_A]; exact h.a_ne)
  have h1' : DivBy (l : K) (derivative K (desc l E)) := by
    have h2 := hon_deriv hσ.toLawD (l : K) _ h1.add
    have h3 := divBy_add h2 (divBy_C_mul' hs hσ.toLawD.deriv_integral)
    rwa [sub_add_cancel] at h3
  have h2 : QCls l (MvPowerSeries.map σ (MvPowerSeries.map σ Φ))
      (PowerSeries.map σ (PowerSeries.map σ A)) a (desc l (desc l E)) :=
    desc_QCls hF hσ.Φ0 hσ.Φint hσ.A0 hσ.Aint h.norm_a h1 h1'
  have c2 := (desc_congr hF.prime hF.norm_l _ h1').1
  refine ⟨desc l (desc l E), ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]; exact h2
  · have hXl : HasSubst ((X : PowerSeries K) ^ l) :=
      HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have c3 := (divBy_expand_iff (l : K) l hl0 _).2 c2
    rw [subst_sub hXl, subst_comp_subst_apply hXl hXl, subst_pow hXl, subst_X hXl, ← pow_mul,
      ← sq] at c3
    have c4 := divBy_add c1 c3
    rwa [sub_add_sub_cancel] at c4

end ReciprocityTheory.ChartRestriction.L1
