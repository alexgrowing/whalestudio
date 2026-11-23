import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace CoboundarySeries

open MvPowerSeries

section Cob

variable {K : Type} [Field K]

theorem has_subst_first_pair : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1] := MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro s; fin_cases s <;> simp)

theorem constantCoeff_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) :
    constantCoeff (in3 F) = 0 := by
  unfold in3
  rw [MvPowerSeries.constantCoeff_subst has_subst_first_pair]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d = 0
  · subst hd
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs), smul_zero]
    have h0 : constantCoeff ((![(X 0 : MvPowerSeries (Fin 3) K), X 1] : Fin 2 → MvPowerSeries (Fin 3) K) s) = 0 := by
      fin_cases s <;> simp
    rw [map_pow, h0, zero_pow hs]

theorem has_subst_coboundary_first {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) :
    HasSubst ![in3 F, (X 2 : MvPowerSeries (Fin 3) K)] := MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro s; fin_cases s <;> simp [constantCoeff_first_two_of_three hF])

theorem has_subst_last_pair (x : Fin 3) : HasSubst ![(X x : MvPowerSeries (Fin 3) K), X 2] := MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro s; fin_cases s <;> simp)

theorem partial_coboundary_sub {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (H H' : MvPowerSeries (Fin 2) K) : d1 F (H - H') = d1 F H - d1 F H' := by
  unfold d1
  rw [MvPowerSeries.subst_sub (has_subst_coboundary_first hF), MvPowerSeries.subst_sub (has_subst_last_pair 0), MvPowerSeries.subst_sub (has_subst_last_pair 1)]
  abel

theorem partial_coboundary_C_mul {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) (a : K)
    (H : MvPowerSeries (Fin 2) K) : d1 F (C a * H) = C a * d1 F H := by
  have key : ∀ (b : Fin 2 → MvPowerSeries (Fin 3) K), HasSubst b →
      subst b (C a * H) = C a * subst b H := by
    intro b hb
    rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul hb]
  unfold d1
  rw [key _ (has_subst_coboundary_first hF), key _ (has_subst_last_pair 0), key _ (has_subst_last_pair 1)]
  ring

theorem subst_subst {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    {a : MvPowerSeries ι K} (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := MvPowerSeries.subst_comp_subst_apply ha.const hb f

theorem subst_single_var {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    (x : ι) (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [subst_subst hb (PowerSeries.HasSubst.X x), MvPowerSeries.subst_X hb]

theorem include_three_coboundary {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) (f : PowerSeries K) :
    in3 (cob F f) = PowerSeries.subst (in3 F) f - at1 0 f - at1 1 f := by
  have hF' : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have h1 : in3 (PowerSeries.subst F f) = PowerSeries.subst (in3 F) f := subst_subst has_subst_first_pair hF' f
  have h2 : in3 (at1 (0 : Fin 2) f) = at1 0 f := by
    unfold in3
    rw [subst_single_var has_subst_first_pair]
    rfl
  have h3 : in3 (at1 (1 : Fin 2) f) = at1 1 f := by
    unfold in3
    rw [subst_single_var has_subst_first_pair]
    rfl
  unfold cob
  show subst _ (PowerSeries.subst F f - at1 0 f - at1 1 f) = _
  rw [MvPowerSeries.subst_sub has_subst_first_pair, MvPowerSeries.subst_sub has_subst_first_pair]
  exact congr_arg₂ (· - ·) (congr_arg₂ (· - ·) h1 h2) h3

theorem partial_coboundary_product {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (f g : PowerSeries K) : d1 F (at1 0 f * at1 1 g) = in3 (cob F f) * at1 2 g := by
  unfold d1
  rw [MvPowerSeries.subst_mul (has_subst_coboundary_first hF), MvPowerSeries.subst_mul (has_subst_last_pair 0), MvPowerSeries.subst_mul (has_subst_last_pair 1),
    subst_single_var (has_subst_coboundary_first hF), subst_single_var (has_subst_coboundary_first hF), subst_single_var (has_subst_last_pair 0), subst_single_var (has_subst_last_pair 0),
    subst_single_var (has_subst_last_pair 1), subst_single_var (has_subst_last_pair 1), include_three_coboundary hF]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  unfold at1
  ring

theorem include_three_zero : in3 (0 : MvPowerSeries (Fin 2) K) = 0 := by
  have h := MvPowerSeries.subst_sub (R := K) (has_subst_first_pair (K := K)) (0 : MvPowerSeries (Fin 2) K) 0
  rw [sub_self, sub_self] at h
  exact h

theorem partial_coboundary_h_series {p : ℕ} (σ : K →+* K) {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (hl : cob F (lgF K p) = 0) (G : MvPowerSeries (Fin 2) K) (γ γ' : K) :
    d1 F (Hser p σ G γ γ') =
      d1 F (DeS p σ G) - C γ * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) := by
  unfold Hser
  rw [partial_coboundary_sub hF, partial_coboundary_sub hF, partial_coboundary_C_mul hF, partial_coboundary_C_mul hF, partial_coboundary_product hF, partial_coboundary_product hF, hl, include_three_zero]
  ring

end Cob

section Supp

variable {K : Type} [Field K]

theorem powq_modEq_one {p : ℕ} (hp : 2 ≤ p) (x : ℕ) : (p ^ 2) ^ x ≡ 1 [MOD p ^ 2 - 1] := by
  have h : p ^ 2 ≡ 1 [MOD p ^ 2 - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))
  simpa using h.pow x

theorem suppOK_sub {p : ℕ} {f g : MvPowerSeries (Fin 2) K} (hf : SuppOK p f) (hg : SuppOK p g) :
    SuppOK p (f - g) := by
  intro n hn
  rw [map_sub] at hn
  by_cases h : MvPowerSeries.coeff n f = 0
  · apply hg n
    intro h'
    apply hn
    rw [h, h', sub_zero]
  · exact hf n h

theorem suppOK_C_mul {p : ℕ} (a : K) {f : MvPowerSeries (Fin 2) K} (hf : SuppOK p f) :
    SuppOK p (C a * f) := by
  intro n hn
  rw [MvPowerSeries.coeff_C_mul] at hn
  exact hf n (right_ne_zero_of_mul hn)

theorem suppOK_frob {p : ℕ} (hp : 2 ≤ p) (σ : K →+* K) {G : MvPowerSeries (Fin 2) K}
    (hG : SuppOK p G) : SuppOK p (frobVar p (map σ G)) := by
  intro n hn
  obtain ⟨m, rfl, hm⟩ := coeff_frobVar_ne_zero (by omega) hn
  rw [MvPowerSeries.coeff_map] at hm
  have hm' : MvPowerSeries.coeff m G ≠ 0 := fun h => hm (by rw [h, map_zero])
  obtain ⟨h0, h1, h2⟩ := hG m hm'
  simp only [Finsupp.smul_apply, smul_eq_mul]
  exact ⟨Nat.mul_pos (by omega) h0, Nat.mul_pos (by omega) h1, h2.mul_left p⟩

private theorem coeff_g0F_ne_lemma {p n : ℕ} (h : PowerSeries.coeff n (g0F K p) ≠ 0) :
    ∃ j, n = p * (p ^ 2) ^ j := by
  rw [g0F, PowerSeries.coeff_mk] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hn : n = p * (p ^ 2) ^ j
  · exact ⟨j, hn⟩
  · exact absurd (if_neg hn) hj

private theorem coeff_lgF_ne_lemma_2 {p n : ℕ} (h : PowerSeries.coeff n (lgF K p) ≠ 0) :
    ∃ j, n = (p ^ 2) ^ j := by
  rw [lgF, PowerSeries.coeff_mk] at h
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hn : n = (p ^ 2) ^ j
  · exact ⟨j, hn⟩
  · exact absurd (if_neg hn) hj

theorem support_ok_g_zero_log {p : ℕ} (hp : 2 ≤ p) : SuppOK p (at1 0 (g0F K p) * at1 1 (lgF K p)) := by
  intro n hn
  rw [coeff_product_single_variables (by decide) (fun z => by fin_cases z <;> simp)] at hn
  obtain ⟨j, hj⟩ := coeff_g0F_ne_lemma (left_ne_zero_of_mul hn)
  obtain ⟨i, hi⟩ := coeff_lgF_ne_lemma_2 (right_ne_zero_of_mul hn)
  refine ⟨?_, ?_, ?_⟩
  · rw [hj]
    exact Nat.mul_pos (by omega) (pow_pos (pow_pos (by omega) _) _)
  · rw [hi]
    exact Nat.one_le_pow _ _ (pow_pos (by omega : 0 < p) 2)
  · rw [hj, hi]
    exact ((powq_modEq_one hp j).mul_left p).trans ((powq_modEq_one hp i).mul_left p).symm

theorem support_ok_log_g_zero {p : ℕ} (hp : 2 ≤ p) : SuppOK p (at1 0 (lgF K p) * at1 1 (g0F K p)) := by
  intro n hn
  rw [coeff_product_single_variables (by decide) (fun z => by fin_cases z <;> simp)] at hn
  obtain ⟨i, hi⟩ := coeff_lgF_ne_lemma_2 (left_ne_zero_of_mul hn)
  obtain ⟨j, hj⟩ := coeff_g0F_ne_lemma (right_ne_zero_of_mul hn)
  refine ⟨?_, ?_, ?_⟩
  · rw [hi]
    exact Nat.one_le_pow _ _ (pow_pos (by omega : 0 < p) 2)
  · rw [hj]
    exact Nat.mul_pos (by omega) (pow_pos (pow_pos (by omega) _) _)
  · rw [hi, hj]
    have h : p * (p * (p ^ 2) ^ j) = (p ^ 2) ^ (j + 1) := by ring
    rw [h]
    exact (powq_modEq_one hp i).trans (powq_modEq_one hp (j + 1)).symm

theorem suppOK_Hser {p : ℕ} (hp : 2 ≤ p) (σ : K →+* K) {G : MvPowerSeries (Fin 2) K}
    (hG : SuppOK p G) (γ γ' : K) : SuppOK p (Hser p σ G γ γ') := by
  unfold Hser DeS
  exact suppOK_sub (suppOK_sub (suppOK_C_mul _ (suppOK_sub (suppOK_frob hp σ hG) (suppOK_C_mul _ hG)))
    (suppOK_C_mul _ (support_ok_g_zero_log hp))) (suppOK_C_mul _ (support_ok_log_g_zero hp))

theorem coeff_lg_lg_eq_zero {p : ℕ} (hp : 2 ≤ p) {n : Fin 2 →₀ ℕ}
    (hn : n 0 ≡ p * n 1 [MOD p ^ 2 - 1]) :
    coeff n (at1 0 (lgF K p) * at1 1 (lgF K p)) = 0 := by
  rw [coeff_product_single_variables (by decide) (fun z => by fin_cases z <;> simp)]
  by_contra h
  obtain ⟨i, hi⟩ := coeff_lgF_ne_lemma_2 (left_ne_zero_of_mul h)
  obtain ⟨j, hj⟩ := coeff_lgF_ne_lemma_2 (right_ne_zero_of_mul h)
  rw [hi, hj] at hn
  have h1 : 1 ≡ p * 1 [MOD p ^ 2 - 1] :=
    ((powq_modEq_one hp i).symm.trans hn).trans ((powq_modEq_one hp j).mul_left p)
  obtain ⟨q, hq⟩ : ∃ q, q = p * p := ⟨_, rfl⟩
  have hpq : p * 2 ≤ q := hq ▸ Nat.mul_le_mul_left p hp
  have hlt1 : 1 < p ^ 2 - 1 := by rw [pow_two, ← hq]; omega
  have hltp : p < p ^ 2 - 1 := by rw [pow_two, ← hq]; omega
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt1, mul_one, Nat.mod_eq_of_lt hltp] at h1
  omega

end Supp

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_add_le_one {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem eq_zero_of_div {p : ℕ} (hp : 2 ≤ p) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {x : K}
    (h : ∀ i : ℕ, ‖x * ((p : K) ^ (i + 1))⁻¹‖ ≤ 1) : x = 0 := by
  by_contra hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hq : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hp1
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hx0 hq
  have h1 := h i
  rw [norm_mul, norm_inv, norm_pow, hnp] at h1
  have hpos : 0 < ((p : ℝ)⁻¹) ^ (i + 1) := by positivity
  rw [mul_inv_le_iff₀ hpos, one_mul] at h1
  have h2 : ((p : ℝ)⁻¹) ^ (i + 1) ≤ ((p : ℝ)⁻¹) ^ i := pow_le_pow_of_le_one hq0 hq.le (by omega)
  linarith

end Norm

section MapG

variable {K : Type} [Field K]

theorem map_Gser (σ : K →+* K) (p : ℕ) (c c' : K) :
    map σ (Gser p c c') = Gser p (σ c) (σ c') := by
  have hA : MvPowerSeries.map σ (Aser K p) = Aser K p := by
    ext n
    rw [MvPowerSeries.coeff_map]
    change σ (Aser K p n) = Aser K p n
    simp only [Aser, map_sum, apply_ite σ, map_inv₀, map_pow, map_natCast, map_zero]
  have hA' : MvPowerSeries.map σ (Aser' K p) = Aser' K p := by
    ext n
    rw [MvPowerSeries.coeff_map]
    change σ (Aser' K p n) = Aser' K p n
    simp only [Aser', map_sum, apply_ite σ, map_inv₀, map_pow, map_natCast, map_zero]
  unfold Gser
  rw [map_sub, map_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_C, hA, hA']

theorem constantCoeff_Gser (p : ℕ) (c c' : K) : constantCoeff (Gser p c c') = 0 := by
  have h1 : MvPowerSeries.constantCoeff (Aser K p) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change Aser K p 0 = 0
    simp [Aser]
  have h2 : MvPowerSeries.constantCoeff (Aser' K p) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change Aser' K p 0 = 0
    simp [Aser']
  unfold Gser
  rw [map_sub, map_mul, map_mul, h1, h2, mul_zero, mul_zero, sub_zero]

end MapG

end CoboundarySeries

open CoboundarySeries

theorem StepH_of (h2 : LemmaTwo) (hSw : SwapRules) (_hL : LawSymm) : StepH := by
  intro K _ _ _ _ p σ hU F hF G γ γ' hG hI1 hI2
  have hp : 2 ≤ p := hU.2.1.le
  obtain ⟨-, -, -, -, -, hHsw⟩ := hSw K p σ G γ γ' hp
  have hsupp : SuppOK p (Hser p σ G γ γ') := suppOK_Hser hp σ hG γ γ'
  have hdiv : DivAB (Hser p σ G γ γ') := by
    intro n hn
    by_contra hc
    obtain ⟨h0, h1, -⟩ := hsupp n hc
    omega
  have hd1 : Integral (d1 F (Hser p σ G γ γ')) := by
    rw [partial_coboundary_h_series σ hF.1 hF.2.2 G γ γ']
    exact hI1
  have hd2 : Integral (d1 F (swap2 (Hser p σ G γ γ'))) := by
    rw [← hHsw, partial_coboundary_h_series σ hF.1 hF.2.2 (swap2 G) γ' γ]
    exact hI2
  obtain ⟨β, R, hR, hHR⟩ := h2 K p σ hU F hF _ hdiv hd1 hd2
  intro n
  by_cases hc : MvPowerSeries.coeff n (Hser p σ G γ γ') = 0
  · rw [hc, norm_zero]
    exact zero_le_one
  · have hll := coeff_lg_lg_eq_zero (K := K) hp (hsupp n hc).2.2
    rw [hHR, map_add, MvPowerSeries.coeff_C_mul, hll, mul_zero, zero_add]
    exact hR n

private theorem coeff_lgF_one_lemma {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) :
    PowerSeries.coeff 1 (lgF K p) = 1 := by
  have h4 : 1 < p ^ 2 := by
    have := Nat.pow_le_pow_left hp 2
    norm_num at this
    omega
  rw [lgF, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]
  simp [h4.ne]

private theorem coeff_g0F_at_lemma_2 {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    PowerSeries.coeff (p * (p ^ 2) ^ i) (g0F K p) = ((p : K) ^ (i + 1))⁻¹ := by
  have hp2 : 2 ≤ p ^ 2 := by nlinarith
  have hinj : ∀ j, (p * (p ^ 2) ^ i = p * (p ^ 2) ^ j) ↔ j = i := by
    intro j
    constructor
    · intro h
      have h' : (p ^ 2) ^ i = (p ^ 2) ^ j := Nat.eq_of_mul_eq_mul_left (by omega) h
      exact (Nat.pow_right_injective hp2 h').symm
    · rintro rfl
      rfl
  have hlt : i < (p ^ 2) ^ i := Nat.lt_pow_self (by omega)
  have hi : i ∈ Finset.range (p * (p ^ 2) ^ i + 1) := by
    rw [Finset.mem_range]
    nlinarith
  rw [g0F, PowerSeries.coeff_mk]
  simp_rw [hinj]
  simp [hi]

private theorem coeff_g0F_one_lemma_3 {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) :
    PowerSeries.coeff 1 (g0F K p) = 0 := by
  rw [g0F, PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun j _ => if_neg ?_
  intro h
  have h1 : 1 ≤ (p ^ 2) ^ j := Nat.one_le_pow _ _ (pow_pos (by omega : 0 < p) 2)
  nlinarith

theorem c_add_sigma_c_eq_zero : StepIII := by
  intro K _ _ _ p σ hU G c c' hc hc' hD hI
  obtain ⟨hpr, hp2, hnp, -, -⟩ := hU
  have hp : 2 ≤ p := hp2.le
  have hp0 : p ≠ 0 := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hnd1 : ¬ p ∣ 1 := fun h => by
    have := Nat.le_of_dvd one_pos h
    omega
  have hall : ∀ z : Fin 2, z = 0 ∨ z = 1 := fun z => by fin_cases z <;> simp
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hlg1 : PowerSeries.coeff 1 (lgF K p) = 1 := coeff_lgF_one_lemma hp
  have hg01 : PowerSeries.coeff 1 (g0F K p) = 0 := coeff_g0F_one_lemma_3 hp
  apply eq_zero_of_div hp hnp
  intro i
  obtain ⟨m, hm⟩ : ∃ m, m = p * (p ^ 2) ^ i := ⟨_, rfl⟩
  have hg0m : PowerSeries.coeff m (g0F K p) = ((p : K) ^ (i + 1))⁻¹ := hm ▸ coeff_g0F_at_lemma_2 hp i
  obtain ⟨n, hn⟩ : ∃ n : Fin 2 →₀ ℕ, n = Finsupp.single 1 m + Finsupp.single 0 1 := ⟨_, rfl⟩

  have hcoefD : MvPowerSeries.coeff (Finsupp.single 1 m) (MvPowerSeries.pderiv (R := K) 0 G -
      MvPowerSeries.C c * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p))) =
      MvPowerSeries.coeff n G - c * ((p : K) ^ (i + 1))⁻¹ := by
    have hs0 : (Finsupp.single (1 : Fin 2) m) 0 = 0 := by simp
    have hs1 : (Finsupp.single (1 : Fin 2) m) 1 = m := by simp
    rw [map_sub, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C_mul, coeff_product_single_variables h01 hall, hs0, hs1,
      PowerSeries.coeff_derivative, hg0m, ← hn]
    simp [hlg1]

  have hcoefH : MvPowerSeries.coeff n (Hser p σ G (σ c) (σ c')) =
      -(MvPowerSeries.coeff n G) - σ c' * ((p : K) ^ (i + 1))⁻¹ := by
    have hn0 : n 0 = 1 := by simp [hn]
    have hn1 : n 1 = m := by simp [hn]
    have hfr : MvPowerSeries.coeff n (frobVar p (MvPowerSeries.map σ G)) = 0 :=
      coeff_frobVar_of_not_dvd hp0 _ (i := 0) (by rw [hn0]; exact hnd1)
    unfold Hser DeS
    simp only [map_sub, MvPowerSeries.coeff_C_mul]
    rw [hfr, coeff_product_single_variables h01 hall, coeff_product_single_variables h01 hall, hn0, hn1, hg01, hlg1, hg0m]
    field_simp
    ring
  have hA : ‖MvPowerSeries.coeff n G - c * ((p : K) ^ (i + 1))⁻¹‖ ≤ 1 := by
    rw [← hcoefD]
    exact hD _
  have hB : ‖-(MvPowerSeries.coeff n G) - σ c' * ((p : K) ^ (i + 1))⁻¹‖ ≤ 1 := by
    rw [← hcoefH]
    exact hI n
  have key : (c + σ c') * ((p : K) ^ (i + 1))⁻¹ =
      -((MvPowerSeries.coeff n G - c * ((p : K) ^ (i + 1))⁻¹) +
        (-(MvPowerSeries.coeff n G) - σ c' * ((p : K) ^ (i + 1))⁻¹)) := by ring
  rw [key, norm_neg]
  exact norm_add_le_one hA hB

theorem StepIV_of (hW : DworkMv) : StepIV := by
  intro K _ _ _ p σ hU G c hG hσc hI
  obtain ⟨hpr, hp2, hnp, -, hσ⟩ := hU
  have hp : 2 ≤ p := hp2.le
  have hp0 : p ≠ 0 := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hcc : MvPowerSeries.constantCoeff (G - Gser p c (σ c)) = 0 := by
    rw [map_sub, constantCoeff_Gser, sub_zero, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hG 0 (Or.inl (by simp))
  refine ⟨hcc, ?_⟩
  rw [hW K (Fin 2) p σ hpr hnp hσ _ hcc]
  have hfs : ∀ f g : MvPowerSeries (Fin 2) K, frobVar p (f - g) = frobVar p f - frobVar p g := by
    intro f g
    simp only [frobVar_eq_expand hp0, map_sub]
  have hmapG : MvPowerSeries.map σ (Gser p c (σ c)) = Gser p (σ c) c := by rw [map_Gser, hσc]
  have hfr := frobenius_expression_g K p c (σ c) hp hpK
  have hDeS : frobVar p (MvPowerSeries.map σ G) - MvPowerSeries.C (p : K) * G =
      MvPowerSeries.C (p : K) * DeS p σ G := by
    unfold DeS
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hpK, map_one, one_mul]
  have key : frobVar p (MvPowerSeries.map σ (G - Gser p c (σ c))) -
      MvPowerSeries.C (p : K) * (G - Gser p c (σ c)) = MvPowerSeries.C (p : K) * Hser p σ G (σ c) (-c) := by
    rw [map_sub, hmapG, hfs]
    unfold Hser
    rw [map_neg]
    linear_combination hDeS - hfr
  intro n
  rw [key, MvPowerSeries.coeff_C_mul, norm_mul, hnp]
  exact mul_le_of_le_one_right (by positivity) (hI n)

end Formalism.InvariantFactorPaths.G7
