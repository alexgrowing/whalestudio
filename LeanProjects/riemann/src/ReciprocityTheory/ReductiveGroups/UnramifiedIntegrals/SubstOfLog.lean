import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.DivByPartialYAtZeroSubstAtXAtY
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonD

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.subst_of_log (h : LawD lam Φ) {e : PowerSeries K} {c : K} (he0 : constantCoeff e = 0)
    (hlog : lam.subst e = C c * lam) : e.subst Φ = Φ.subst ![atX e, atY e] := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hx0 : MvPowerSeries.constantCoeff (atX e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hy0 : MvPowerSeries.constantCoeff (atY e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hb : MvPowerSeries.HasSubst ![atX e, atY e] := Formalism.G.LogP.hs2 hx0 hy0
  have hb0 : ∀ i, MvPowerSeries.constantCoeff (![atX e, atY e] i) = 0 := by
    intro i; fin_cases i <;> simpa
  refine Formalism.G.LogP.psubst_injective h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero h.Φ0 _ he0)
    (MvPowerSeries.constantCoeff_subst_eq_zero hb hb0 h.Φ0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hΦs, hlog', PowerSeries.subst_smul hΦs, h.log,
    ← Formalism.G.LogP.psubst_subst lam h.Φ0 hb, h.log, MvPowerSeries.subst_add hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  show _ = lam.subst (e.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
    + lam.subst (e.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
  rw [← PowerSeries.subst_comp_subst_apply hes (hX 0), ← PowerSeries.subst_comp_subst_apply hes (hX 1),
    hlog', PowerSeries.subst_smul (hX 0), PowerSeries.subst_smul (hX 1), smul_add]

theorem LawD.comm_of_log (h : LawD lam Φ) {e f : PowerSeries K} {c d : K}
    (he0 : constantCoeff e = 0) (hf0 : constantCoeff f = 0)
    (hlog : lam.subst e = C c * lam) (hlogf : lam.subst f = C d * lam) :
    e.subst f = f.subst e := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hlogf' : lam.subst f = d • lam := by rw [hlogf, smul_eq_C_mul]
  refine Formalism.G.LogP.psubst_injective (σ := Unit) h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero hf0 _ he0)
    (PowerSeries.constantCoeff_subst_eq_zero he0 _ hf0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hfs, ← PowerSeries.subst_comp_subst_apply hfs hes,
    hlog', hlogf', PowerSeries.subst_smul hfs, PowerSeries.subst_smul hes, hlog', hlogf',
    smul_smul, smul_smul, mul_comm]

theorem mulL_homCls (h : HD σ lam Φ A a) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) : HomCls l Φ A Φ A e where
  g0 := he0
  gInt := he
  add := by
    rw [h.toLawD.subst_of_log he0 hlog, sub_self]
    exact divByMv_zero _
  eig := by
    rw [h.toLawD.comm_of_log he0 h.A0 hlog h.Alog, sub_self]
    intro n
    simp

theorem mulL_deriv (h : LawD lam Φ) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    DivBy (l : K) (derivative K e) := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have h1 : (derivative K lam).subst e * derivative K e = C (l : K) * derivative K lam := by
    rw [← PowerSeries.derivative_subst hes, hlog]
    simp
  have hi : IntegralPS ((derivative K lam).subst e) :=
    (integralPS_iff_mv _).2 (integralMv_subst h.deriv_integral he0 ((integralPS_iff_mv _).1 he))
  have hc : constantCoeff ((derivative K lam).subst e) = 1 := by
    rw [← h.deriv_const]
    exact Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (τ := Unit) (derivative K lam)
      (b := fun _ => e) (fun _ => he0)
  refine divBy_of_mul_unit hi (by rw [hc, norm_one]) ?_
  rw [h1]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (h.deriv_integral n)

theorem hon_shape (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    ∃ hh : PowerSeries K,
      HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh ∧
      DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2))) ∧
      coeff 1 hh = coeff (l ^ 2) e := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hσ := h.map hF
  obtain ⟨hc1, hH1⟩ := hom_desc hF h.Φ0 h.Φint h.Φ0 h.Φint h.A0 h.Aint h.A0 h.Aint
    (mulL_homCls h he0 he hlog) (mulL_deriv h.toLawD he0 he hlog)
  have hsmall : ‖coeff 1 (desc l e)‖ ≤ ‖(l : K)‖ := by
    refine hom_eigen hσ.A0 h.A0 hH1 ?_
    rw [hσ.coeff_one_A, h.coeff_one_A]
    exact h.a_ne
  have hd1 : DivBy (l : K) (derivative K (desc l e)) :=
    hom_deriv hF.norm_l.le hσ.toLawD h.toLawD hH1 hsmall
  obtain ⟨hc2, hH2⟩ := hom_desc hF hσ.Φ0 hσ.Φint h.Φ0 h.Φint hσ.A0 hσ.Aint h.A0 h.Aint hH1 hd1
  refine ⟨desc l (desc l e), ?_, ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]
    exact hH2
  · have hXs : PowerSeries.HasSubst ((X : PowerSeries K) ^ l) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have h3 := (divBy_expand_iff (l : K) l hl0 _).2 hc2
    rw [PowerSeries.subst_sub hXs, PowerSeries.subst_comp_subst_apply hXs hXs,
      PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs, ← pow_mul, ← sq] at h3
    have h4 := divBy_add hc1 h3
    rwa [sub_add_sub_cancel] at h4
  · rw [coeff_one_desc, desc, coeff_mk, sq]

theorem hon_level (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) : ‖coeff (l ^ 2) e‖ = 1 := by
  obtain ⟨hh, -, hc, -⟩ := hon_shape hF h he0 he hlog
  obtain ⟨i, hi, hi1⟩ := hlev
  have hq0 : l ^ 2 ≠ 0 := pow_ne_zero _ hF.prime.ne_zero
  by_cases hdvd : l ^ 2 ∣ i
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [coeff_zero_eq_constantCoeff_apply, he0, norm_zero] at hi1
      exact absurd hi1 zero_ne_one
    · rw [← le_antisymm hi (Nat.le_of_dvd hpos hdvd)]
      exact hi1
  · have h1 := hc i
    rw [map_sub, coeff_subst_X_pow hq0, if_neg hdvd, sub_zero, hi1] at h1
    exact absurd h1 (not_le.2 hF.norm_l)

end ReciprocityTheory.ChartRestriction.L1
