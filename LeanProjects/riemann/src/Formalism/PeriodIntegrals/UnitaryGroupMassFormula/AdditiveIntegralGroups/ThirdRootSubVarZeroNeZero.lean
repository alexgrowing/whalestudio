import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffWSeriesVarZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

section order

variable {σ : Type*}

theorem rt_two_le_mul_left (f g : MvPowerSeries σ ℂ_[p]) (hg : 2 ≤ g.order) : 2 ≤ (f * g).order := by
  first
    | exact (hg.trans le_add_self).trans (MvPowerSeries.le_order_mul ..)
    | exact (hg.trans le_add_self).trans (MvPowerSeries.order_mul_ge ..)
    | exact (hg.trans le_add_self).trans (MvPowerSeries.add_order_le_order_mul ..)

theorem rt_two_le_mul_right (f g : MvPowerSeries σ ℂ_[p]) (hf : 2 ≤ f.order) : 2 ≤ (f * g).order := by
  first
    | exact (hf.trans le_self_add).trans (MvPowerSeries.le_order_mul ..)
    | exact (hf.trans le_self_add).trans (MvPowerSeries.order_mul_ge ..)
    | exact (hf.trans le_self_add).trans (MvPowerSeries.add_order_le_order_mul ..)

theorem rt_two_le_add {f g : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) (hg : 2 ≤ g.order) :
    2 ≤ (f + g).order := by
  refine MvPowerSeries.le_order fun d hd => ?_
  rw [map_add, MvPowerSeries.coeff_of_lt_order (hd.trans_le hf),
    MvPowerSeries.coeff_of_lt_order (hd.trans_le hg), add_zero]

theorem rt_two_le_neg {f : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) : 2 ≤ (-f).order := by
  rw [MvPowerSeries.order_neg]
  exact hf

theorem rt_two_le_sub {f g : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) (hg : 2 ≤ g.order) :
    2 ≤ (f - g).order := by
  rw [sub_eq_add_neg]
  exact rt_two_le_add hf (rt_two_le_neg hg)

theorem rt_one_le_X (i : σ) : 1 ≤ (Xv i : MvPowerSeries σ ℂ_[p]).order := by
  refine MvPowerSeries.le_order fun d hd => ?_
  rw [MvPowerSeries.coeff_X, if_neg]
  rintro rfl
  simp at hd

theorem rt_two_le_mul_X {f : MvPowerSeries σ ℂ_[p]} (hf : 1 ≤ f.order) (i : σ) :
    2 ≤ (f * Xv i).order := by
  have h2 : (2 : ℕ∞) ≤ f.order + (Xv i : MvPowerSeries σ ℂ_[p]).order :=
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ _ := add_le_add hf (rt_one_le_X i)
  first
    | exact h2.trans (MvPowerSeries.le_order_mul ..)
    | exact h2.trans (MvPowerSeries.order_mul_ge ..)
    | exact h2.trans (MvPowerSeries.add_order_le_order_mul ..)

end order

theorem rt_order_lam (wq : PowerSeries ℂ_[p]) : 2 ≤ (lam wq).order := by
  refine MvPowerSeries.le_order fun e he => ?_
  have hd : e 0 + e 1 < 2 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at he
    exact_mod_cast he
  rw [lamA_coeff_lam, lamA_coeff_wser, if_neg (by omega)]

private theorem rt_constantCoeff_lam_lemma {f : MvPowerSeries (Fin 2) ℂ_[p]} (hf : 2 ≤ f.order) :
    MvPowerSeries.constantCoeff f = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ hf
  simp

theorem rt_constantCoeff_lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (lam wq) = 0 := by
  exact rt_constantCoeff_lam_lemma (rt_order_lam wq)

theorem rt_wv (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    wv wq i = (Xv i) ^ 3 * PowerSeries.subst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) wq := by
  have ha : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  unfold wv wser
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha]

theorem rt_order_nu (wq : PowerSeries ℂ_[p]) : 2 ≤ (nu wq).order := by
  have h3 : 2 ≤ ((Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 3).order := by
    rw [pow_succ]
    exact rt_two_le_mul_right _ _ (by rw [pow_two]; exact rt_two_le_mul_X (rt_one_le_X 0) 0)
  unfold nu
  rw [rt_wv]
  exact rt_two_le_sub (rt_two_le_mul_right _ _ h3) (rt_two_le_mul_right _ _ (rt_order_lam wq))

theorem rt_constantCoeff_nu (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (nu wq) = 0 := by
  exact rt_constantCoeff_lam_lemma (rt_order_nu wq)

theorem rt_order_Bcf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : 2 ≤ (Bcf W wq).order := by
  unfold Bcf
  have hl := rt_order_lam wq
  have hn := rt_order_nu wq
  have hl2 : 2 ≤ (lam wq ^ 2).order := by rw [pow_two]; exact rt_two_le_mul_left _ _ hl
  refine rt_two_le_add (rt_two_le_add (rt_two_le_add (rt_two_le_add ?_ ?_) ?_) ?_) ?_
  · exact rt_two_le_mul_left _ _ hl
  · exact rt_two_le_mul_left _ _ hn
  · exact rt_two_le_mul_left _ _ hl2
  · exact rt_two_le_mul_left _ _ hn
  · exact rt_two_le_mul_left _ _ hn

theorem constantCoeff_Acf (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Acf W wq) = 1 := by
  simp [Acf, rt_constantCoeff_lam]

theorem rt_Acf_ne (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Acf W wq) ≠ 0 := by
  rw [constantCoeff_Acf]
  exact one_ne_zero

theorem rt_order_BA (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    2 ≤ (Bcf W wq * (Acf W wq)⁻¹).order := by
  exact rt_two_le_mul_right _ _ (rt_order_Bcf W wq)

theorem constantCoeff_thirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Z3 W wq) = 0 := by
  simp [Z3, rt_constantCoeff_lam_lemma (rt_order_Bcf W wq)]

theorem vieta1 (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    Acf W wq * (Xv 0 + Xv 1 + Z3 W wq) = -Bcf W wq := by
  have hA : Acf W wq * (Acf W wq)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (rt_Acf_ne W wq)
  unfold Z3
  linear_combination (-(Bcf W wq)) * hA

theorem var_zero_sub_var_one_ne_zero : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
  have hs : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]
    decide
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h0
  simp [MvPowerSeries.coeff_X, hs] at h1

private theorem chordCubic_var_zero_lemma (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (u : MvPowerSeries (Fin 2) ℂ_[p]) :
    G W u (lam wq * u + nu wq) = Acf W wq * u ^ 3 + Bcf W wq * u ^ 2 + Ccf W wq * u + Dcf W wq := by
  unfold G Acf Bcf Ccf Dcf
  ring

theorem chordCubic_var_zero {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Acf W wq * Xv 0 ^ 3 + Bcf W wq * Xv 0 ^ 2 + Ccf W wq * Xv 0 + Dcf W wq = 0 := by
  have hw : wv wq 0 = lam wq * Xv 0 + nu wq := by
    unfold nu
    ring
  rw [← chordCubic_var_zero_lemma, ← hw]
  exact G_wv h 0

theorem chordCubic_var_one {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Acf W wq * Xv 1 ^ 3 + Bcf W wq * Xv 1 ^ 2 + Ccf W wq * Xv 1 + Dcf W wq = 0 := by
  have hw : wv wq 1 = lam wq * Xv 1 + nu wq := by
    unfold nu
    linear_combination (-1 : MvPowerSeries (Fin 2) ℂ_[p]) * lam_mul wq
  rw [← chordCubic_var_zero_lemma, ← hw]
  exact G_wv h 1

theorem vieta2 {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Ccf W wq = Acf W wq * (Xv 0 * Xv 1 + Xv 0 * Z3 W wq + Xv 1 * Z3 W wq) := by
  have hK : Acf W wq * (Xv 0 ^ 2 + Xv 0 * Xv 1 + Xv 1 ^ 2) + Bcf W wq * (Xv 0 + Xv 1) + Ccf W wq = 0 := by
    have hprod : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) *
        (Acf W wq * (Xv 0 ^ 2 + Xv 0 * Xv 1 + Xv 1 ^ 2) + Bcf W wq * (Xv 0 + Xv 1) + Ccf W wq) = 0 := by
      linear_combination chordCubic_var_zero h - chordCubic_var_one h
    exact (mul_eq_zero.1 hprod).resolve_left var_zero_sub_var_one_ne_zero
  linear_combination hK - (Xv 0 + Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) * vieta1 W wq

theorem vieta3 {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Dcf W wq = -(Acf W wq * Xv 0 * Xv 1 * Z3 W wq) := by
  linear_combination chordCubic_var_zero h - (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * vieta1 W wq -
    (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * vieta2 h

theorem zwEquation_thirdRoot {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    G W (Z3 W wq) (lam wq * Z3 W wq + nu wq) = 0 := by
  rw [chordCubic_var_zero_lemma]
  linear_combination Z3 W wq ^ 2 * vieta1 W wq + Z3 W wq * vieta2 h + vieta3 h

theorem rt_G_map {R R' : Type*} [CommRing R] [Algebra ℂ_[p] R] [CommRing R'] [Algebra ℂ_[p] R']
    (φ : R →ₐ[ℂ_[p]] R') (W : WeierstrassCurve ℂ_[p]) (u v : R) :
    φ (G W u v) = G W (φ u) (φ v) := by
  simp only [G, map_add, map_sub, map_mul, map_pow, AlgHom.commutes]

theorem subst_thirdRoot_wSeries {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (Z3 W wq) (wser wq) = lam wq * Z3 W wq + nu wq := by
  obtain ⟨z, hz⟩ : ∃ z, z = Z3 W wq := ⟨_, rfl⟩
  have hGv := zwEquation_thirdRoot h
  rw [← hz] at hGv ⊢
  have hz0 : MvPowerSeries.constantCoeff z = 0 := by rw [hz]; exact constantCoeff_thirdRoot W wq
  have ha : PowerSeries.HasSubst z := PowerSeries.HasSubst.of_constantCoeff_zero hz0
  obtain ⟨w, hw⟩ : ∃ w, w = PowerSeries.subst z (wser wq) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = lam wq * z + nu wq := ⟨_, rfl⟩
  rw [← hw, ← hv]
  rw [← hv] at hGv
  have hGw : G W z w = 0 := by
    have h0 := congrArg (PowerSeries.substAlgHom ha) (G_wser h)
    rw [rt_G_map, map_zero, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X ha, ← hw] at h0
    exact h0
  have hw' : w = z ^ 3 * PowerSeries.subst z wq := by
    rw [hw, wser, ← PowerSeries.coe_substAlgHom ha, map_mul, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X ha]
  have hw0 : MvPowerSeries.constantCoeff w = 0 := by
    rw [hw', map_mul, map_pow, hz0]
    simp
  have hv0 : MvPowerSeries.constantCoeff v = 0 := by
    simp [hv, hz0, rt_constantCoeff_lam, rt_constantCoeff_nu]
  have hfac : G W z v - G W z w = (v - w) *
      (algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₁ * z +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₂ * z ^ 2 +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₃ * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₄ * z * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₆ * (v ^ 2 + v * w + w ^ 2) - 1) := by
    unfold G
    ring
  have hF : (algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₁ * z +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₂ * z ^ 2 +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₃ * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₄ * z * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₆ * (v ^ 2 + v * w + w ^ 2) - 1) ≠ 0 := by
    intro h0
    have h1 := congrArg MvPowerSeries.constantCoeff h0
    simp [hz0, hv0, hw0] at h1
  rw [hGv, hGw, sub_zero] at hfac
  exact (sub_eq_zero.1 ((mul_eq_zero.1 hfac.symm).resolve_right hF)).symm

theorem rt_coeff_BA (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) (Bcf W wq * (Acf W wq)⁻¹) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (rt_order_BA W wq)
  norm_num [Finsupp.degree_single]

theorem thirdRoot_sub_var_zero_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Z3 W wq - Xv 0 ≠ 0 := by
  have hs : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]
    decide
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) h0
  simp [Z3, rt_coeff_BA, MvPowerSeries.coeff_X, hs, hs.symm] at h1

theorem thirdRoot_sub_var_one_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Z3 W wq - Xv 1 ≠ 0 := by
  have hs : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]
    decide
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h0
  simp [Z3, rt_coeff_BA, MvPowerSeries.coeff_X, hs, hs.symm] at h1

theorem thirdRoot_mem_coeffSubring {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    Z3 W wq ∈ SerS S (Fin 2) := by
  have hwq := wq_mem h1 h2 h3 h4 h6 h
  have hcc : ∀ a ∈ S, cc a ∈ SerS S (Fin 2) := fun a ha => (mem_SerS S _).2 fun e => by
    simp only [cc, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      MvPowerSeries.coeff_C]
    split_ifs
    · exact ha
    · exact S.zero_mem
  have hX : ∀ i, (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := fun i =>
    (mem_SerS S _).2 fun e => by
      rw [MvPowerSeries.coeff_X]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
  have hl : lam wq ∈ SerS S (Fin 2) := (mem_SerS S _).2 (lam_mem hwq)
  have hw0 : wv wq 0 ∈ SerS S (Fin 2) := (mem_SerS S _).2 fun e => by
    rw [coeff_wSeriesVar_zero]
    split_ifs
    · exact lamA_wser_mem hwq _
    · exact S.zero_mem
  have hn : nu wq ∈ SerS S (Fin 2) := sub_mem hw0 (mul_mem hl (hX 0))
  have h2' : (2 : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
    rw [show (2 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 + 1 from one_add_one_eq_two.symm]
    exact add_mem (SerS S (Fin 2)).one_mem (SerS S (Fin 2)).one_mem
  have h3' : (3 : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
    rw [show (3 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 + 1 + 1 by ring]
    exact add_mem (add_mem (SerS S (Fin 2)).one_mem (SerS S (Fin 2)).one_mem) (SerS S (Fin 2)).one_mem
  have hA : Acf W wq ∈ SerS S (Fin 2) := by
    unfold Acf
    exact add_mem (add_mem (add_mem (SerS S (Fin 2)).one_mem (mul_mem (hcc _ h2) hl)) (mul_mem (hcc _ h4) (pow_mem hl 2)))
      (mul_mem (hcc _ h6) (pow_mem hl 3))
  have hB : Bcf W wq ∈ SerS S (Fin 2) := by
    unfold Bcf
    exact add_mem (add_mem (add_mem (add_mem (mul_mem (hcc _ h1) hl) (mul_mem (hcc _ h2) hn))
      (mul_mem (hcc _ h3) (pow_mem hl 2))) (mul_mem (mul_mem (mul_mem h2' (hcc _ h4)) hl) hn))
      (mul_mem (mul_mem (mul_mem h3' (hcc _ h6)) (pow_mem hl 2)) hn)
  unfold Z3
  exact sub_mem (sub_mem (neg_mem (hX 0)) (hX 1)) (mul_mem hB (inv_mem_SerS S (constantCoeff_Acf W wq) hA))

end PI.AddIntG.Wk
