import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LocalComponentGL
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_mul bd_C bd_sum int_mul int_pow sm_mul bd_natCast frob_congr
  PhiH PhiH_apply)

namespace DividedPowerNorms

section Scalars

variable {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}

theorem norm_p_lt_one (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) : ‖(p : K)‖ < 1 := by
  rw [hnp]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem norm_p_pos (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) : 0 < ‖(p : K)‖ := by
  rw [hnp]
  exact inv_pos.mpr (by exact_mod_cast hp.pos)

theorem norm_p_pow_le_one (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (e : ℕ) :
    ‖(p : K) ^ e‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le

theorem norm_pow_div (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (m : ℕ) :
    ‖(p : K) ^ (m + 1) / ((m + 1 : ℕ) : K)‖ ≤ (p : ℝ)⁻¹ := by
  have hlt := norm_p_lt_one (K := K) hp hnp
  have hpos := norm_p_pos (K := K) hp hnp
  rw [norm_div, norm_pow,
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt (show m + 1 ≠ 0 by omega)]
  have hv : padicValNat p (m + 1) ≤ m := by
    have h1 : p ^ padicValNat p (m + 1) ∣ m + 1 := pow_padicValNat_dvd
    have h2 := Nat.le_of_dvd (Nat.succ_pos m) h1
    have h3 : padicValNat p (m + 1) < p ^ padicValNat p (m + 1) := Nat.lt_pow_self hp.one_lt
    omega
  rw [div_le_iff₀ (pow_pos hpos _), ← hnp, ← pow_succ']
  exact pow_le_pow_of_le_one hpos.le hlt.le (by omega)

theorem norm_scalar [CharZero K] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {c : K} (k m : ℕ)
    (hc : ‖((k + 1 : ℕ) : K) * c‖ ≤ 1) :
    ‖c * ((k + 1).choose (m + 1) : K) * (p : K) ^ (m + 1)‖ ≤ (p : ℝ)⁻¹ := by
  have hm : ((m + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have h' : ((k + 1 : ℕ) : K) * (k.choose m : K) =
      ((k + 1).choose (m + 1) : K) * ((m + 1 : ℕ) : K) := by
    exact_mod_cast Nat.add_one_mul_choose_eq k m
  have e : c * ((k + 1).choose (m + 1) : K) * (p : K) ^ (m + 1) =
      (((k + 1 : ℕ) : K) * c) * (k.choose m : K) * ((p : K) ^ (m + 1) / ((m + 1 : ℕ) : K)) := by
    rw [mul_div_assoc', eq_div_iff hm]
    linear_combination (-(c * (p : K) ^ (m + 1))) * h'
  rw [e, norm_mul, norm_mul]
  calc ‖((k + 1 : ℕ) : K) * c‖ * ‖(k.choose m : K)‖ * ‖(p : K) ^ (m + 1) / ((m + 1 : ℕ) : K)‖
      ≤ 1 * 1 * (p : ℝ)⁻¹ :=
        mul_le_mul (mul_le_mul hc (IsUltrametricDist.norm_natCast_le_one K _) (norm_nonneg _)
          zero_le_one) (norm_pow_div hp hnp m) (norm_nonneg _) (by norm_num)
    _ = (p : ℝ)⁻¹ := by ring

end Scalars

section Incr

variable {K κ : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}

theorem bd_pow_incr (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {A Y : MvPowerSeries κ K}
    (hA : Bd 1 A) (hY : Bd 1 Y) (c : K) (k : ℕ) (hc : ‖(k : K) * c‖ ≤ 1) :
    Bd (p : ℝ)⁻¹ (MvPowerSeries.C c * ((A + MvPowerSeries.C (p : K) * Y) ^ k - A ^ k)) := by
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  rcases k with _ | k
  · intro n
    simp
  have e : MvPowerSeries.C c * ((A + MvPowerSeries.C (p : K) * Y) ^ (k + 1) - A ^ (k + 1)) =
      ∑ m ∈ range (k + 1), MvPowerSeries.C (c * ((k + 1).choose (m + 1) : K) * (p : K) ^ (m + 1)) *
        (Y ^ (m + 1) * A ^ (k + 1 - (m + 1))) := by
    rw [add_comm A, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.sub_zero]
    rw [add_sub_cancel_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [e]
  exact bd_sum hpos _ _ fun m _ =>
    sm_mul hpos (bd_C hpos (norm_scalar hp hnp k m hc)) (int_mul (int_pow hY _) (int_pow hA _))

end Incr

end DividedPowerNorms

open DividedPowerNorms

theorem divided_derivative : DivDeriv := by
  intro K ι κ _ _ _ _ _ p hp hnp x Φ φ Y hΦ hφ0 hφ hY0 hY n
  classical
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  set φ' := Function.update φ x (φ x + MvPowerSeries.C (p : K) * Y) with hφ'
  have hs : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have hs' : MvPowerSeries.HasSubst φ' := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => ?_
    by_cases h : i = x
    · subst h
      simp [hφ', hφ0, hY0]
    · simp [hφ', Function.update_of_ne h, hφ0]
  rw [map_sub, MvPowerSeries.coeff_subst hs', MvPowerSeries.coeff_subst hs,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hs' Φ n)
      (MvPowerSeries.coeff_subst_finite hs Φ n)]
  refine Formalism.DworkPowerSeriesWeights.norm_finsum_le_of hpos fun d => ?_
  have e1 : ∀ ψ : ι → MvPowerSeries κ K, (d.prod fun s e => ψ s ^ e) =
      ψ x ^ d x * (d.erase x).prod fun s e => ψ s ^ e := fun ψ =>
    (Finsupp.mul_prod_erase' d x (fun s e => ψ s ^ e) fun _ => pow_zero _).symm
  have e2 : ((d.erase x).prod fun s e => φ' s ^ e) = (d.erase x).prod fun s e => φ s ^ e := by
    refine Finsupp.prod_congr fun s hs => ?_
    have : s ≠ x := by
      rintro rfl
      simp at hs
    rw [hφ', Function.update_of_ne this]
  have hR : Bd 1 ((d.erase x).prod fun s e => φ s ^ e) := by
    unfold Finsupp.prod
    refine Finset.prod_induction _ (Bd 1) (fun a b ha hb => int_mul ha hb) DworkIntegrality.bd_one
      fun s _ => int_pow (hφ s) _
  have hc : ‖(d x : K) * MvPowerSeries.coeff d Φ‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos (d x) with h0 | h0
    · simp [h0]
    · have h1 := hΦ (d - Finsupp.single x 1)
      rw [MvPowerSeries.coeff_pderiv] at h1
      have h2 : d - Finsupp.single x 1 + Finsupp.single x 1 = d := by
        ext s
        by_cases h : s = x
        · subst h
          simp
          omega
        · simp [Ne.symm h]
      have h3 : (((d - Finsupp.single x 1 : ι →₀ ℕ) x : ℕ) : K) + 1 = (d x : K) := by
        have : (d - Finsupp.single x 1 : ι →₀ ℕ) x + 1 = d x := by
          simp
          omega
        exact_mod_cast this
      rw [h2, h3, mul_comm] at h1
      exact h1
  have e3 : MvPowerSeries.coeff d Φ • MvPowerSeries.coeff n (d.prod fun s e => φ' s ^ e) -
      MvPowerSeries.coeff d Φ • MvPowerSeries.coeff n (d.prod fun s e => φ s ^ e) =
      MvPowerSeries.coeff n (MvPowerSeries.C (MvPowerSeries.coeff d Φ) *
        ((φ x + MvPowerSeries.C (p : K) * Y) ^ d x - φ x ^ d x) *
          (d.erase x).prod fun s e => φ s ^ e) := by
    rw [e1 φ', e1 φ, e2, mul_assoc, MvPowerSeries.coeff_C_mul, sub_mul, map_sub, smul_eq_mul,
      smul_eq_mul, mul_sub]
    simp [hφ']
  rw [e3]
  exact sm_mul hpos (bd_pow_incr hp hnp (hφ x) hY _ _ hc) hR n

namespace DividedPowerNorms

theorem norm_coeff_lgF_mul {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (N : ℕ) : ‖PowerSeries.coeff N (lgF K p) * (N : K)‖ ≤ 1 := by
  have hpK : (p : K) ≠ 0 := norm_pos_iff.mp (norm_p_pos hp hnp)
  by_cases h : PowerSeries.coeff N (lgF K p) = 0
  · simp [h]
  obtain ⟨j, rfl⟩ := coeff_lgF_ne_zero h
  rw [coeff_lgF_pow K hp.two_le]
  have e : ((p : K) ^ j)⁻¹ * (((p ^ 2) ^ j : ℕ) : K) = (p : K) ^ j := by
    push_cast
    field_simp
    ring
  rw [e]
  exact norm_p_pow_le_one hp hnp j

theorem integral_pderiv_lgF {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) :
    Integral (MvPowerSeries.pderiv (R := K) () (lgF K p : MvPowerSeries Unit K)) := by
  intro n
  rw [MvPowerSeries.coeff_pderiv]
  have h1 : n + Finsupp.single () 1 = Finsupp.single () (n () + 1) := by
    ext
    simp
  have h2 := norm_coeff_lgF_mul (K := K) hp hnp (n () + 1)
  rw [h1]
  rw [PowerSeries.coeff] at h2
  exact_mod_cast h2

end DividedPowerNorms

theorem DeIntegral_of (hD : DivDeriv) (hL : LawSymm) : DeIntegral := by
  intro K _ _ _ p σ hp hnp hσ F hF
  have hσF : MvPowerSeries.map σ F = F := (hL K p hp hnp F hF).1 σ
  obtain ⟨hF0, hFi, hFc⟩ := hF
  have hpK : (p : K) ≠ 0 := norm_pos_iff.mp (norm_p_pos hp hnp)
  have hg0 := (g_zero_relation_holds K p hp.two_le hpK).1
  have hsXp : PowerSeries.HasSubst (PowerSeries.X ^ p : PowerSeries K) :=
    PowerSeries.HasSubst.X_pow hp.ne_zero
  have hsF : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hsX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.X i
  have hsP : MvPowerSeries.HasSubst
      (fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ^ p) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp [hp.ne_zero]

  have key : ∀ a : MvPowerSeries (Fin 2) K, PowerSeries.HasSubst a →
      PowerSeries.subst a (g0F K p) =
        MvPowerSeries.C ((p : K)⁻¹) * PowerSeries.subst (a ^ p) (lgF K p) := by
    intro a ha
    rw [hg0, PowerSeries.subst_mul ha, PowerSeries.subst_C,
      PowerSeries.subst_comp_subst_apply hsXp ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

  have key2 : ∀ a : MvPowerSeries (Fin 2) K, PowerSeries.HasSubst a →
      frobVar p (PowerSeries.subst a (lgF K p)) = PowerSeries.subst (frobVar p a) (lgF K p) := by
    intro a ha
    unfold frobVar
    rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha.const hsP]
    rfl
  have hX : ∀ i : Fin 2, frobVar p (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X i ^ p := fun i => by
    unfold frobVar
    rw [MvPowerSeries.subst_X hsP]
  have hat : ∀ i : Fin 2, at1 i (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * frobVar p (at1 i (lgF K p)) := fun i => by
    unfold at1
    rw [key _ (hsX i), key2 _ (hsX i), hX]
  have hlog : PowerSeries.subst F (lgF K p) = at1 0 (lgF K p) + at1 1 (lgF K p) := by
    unfold cob at hFc
    linear_combination hFc
  have hsum : at1 0 (g0F K p) + at1 1 (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * PowerSeries.subst (frobVar p F) (lgF K p) := by
    rw [← key2 F hsF, hlog, hat, hat, frobVar_eq_expand hp.ne_zero, frobVar_eq_expand hp.ne_zero,
      frobVar_eq_expand hp.ne_zero, map_add, mul_add]

  set r : MvPowerSeries (Fin 2) K := MvPowerSeries.C ((p : K)⁻¹) * (frobVar p F - F ^ p) with hr
  have hCC : MvPowerSeries.C (p : K) * MvPowerSeries.C ((p : K)⁻¹) =
      (1 : MvPowerSeries (Fin 2) K) := by
    rw [← map_mul, mul_inv_cancel₀ hpK, map_one]
  have hFr : frobVar p F = F ^ p + MvPowerSeries.C (p : K) * r := by
    rw [hr, ← mul_assoc, hCC]
    ring
  have hinv : ‖((p : K)⁻¹)‖ = (p : ℝ) := by rw [norm_inv, hnp, inv_inv]
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hscale : ∀ f : MvPowerSeries (Fin 2) K, Bd (p : ℝ)⁻¹ f →
      Integral (MvPowerSeries.C ((p : K)⁻¹) * f) := by
    intro f hf n
    rw [MvPowerSeries.coeff_C_mul, norm_mul, hinv]
    calc (p : ℝ) * ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (hf n) hppos.le
      _ = 1 := mul_inv_cancel₀ hppos.ne'
  have hri : Integral r := by
    refine hscale _ fun n => ?_
    have h := frob_congr (σ := σ) hp hnp hσ (f := F) hFi n
    rw [PhiH_apply, hσF, map_sub, norm_sub_rev, ← map_sub] at h
    exact h
  have hr0 : MvPowerSeries.constantCoeff r = 0 := by
    have h1 : MvPowerSeries.constantCoeff (frobVar p F) = 0 := by
      have := coeff_frobVar_smul hp.ne_zero F 0
      rw [smul_zero] at this
      simpa [hF0] using this
    rw [hr, map_mul, map_sub, h1, map_pow, hF0, zero_pow hp.ne_zero, sub_zero, mul_zero]
  have hmain := hD K Unit (Fin 2) p hp hnp () (lgF K p) (fun _ => F ^ p) r
    (integral_pderiv_lgF hp hnp) (fun _ => by rw [map_pow, hF0, zero_pow hp.ne_zero])
    (fun _ => int_pow hFi p) hr0 hri
  have hupd : Function.update (fun _ : Unit => F ^ p) () (F ^ p + MvPowerSeries.C (p : K) * r) =
      fun _ => frobVar p F := by
    funext u
    simp [hFr]
  rw [hupd] at hmain
  have e : cob F (g0F K p) = MvPowerSeries.C ((p : K)⁻¹) *
      (-(MvPowerSeries.subst (fun _ : Unit => frobVar p F) (lgF K p : MvPowerSeries Unit K) -
        MvPowerSeries.subst (fun _ : Unit => F ^ p) (lgF K p : MvPowerSeries Unit K))) := by
    unfold cob
    rw [sub_sub, hsum, key F hsF, PowerSeries.subst_def, PowerSeries.subst_def]
    ring
  rw [e]
  exact hscale _ (DworkIntegrality.bd_neg hmain)

theorem derivative_a : DerivA := by
  intro K _ _ _ p hp hnp
  have hp2 := hp.two_le
  have hpK : (p : K) ≠ 0 := norm_pos_iff.mp (norm_p_pos hp hnp)
  have a0 : ∀ n : Fin 2 →₀ ℕ, (n + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 = n 0 + 1 := fun n => by simp
  have a1 : ∀ n : Fin 2 →₀ ℕ, (n + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 1 = n 1 := fun n => by simp
  have hcast : ∀ n : Fin 2 →₀ ℕ, (n 0 : K) + 1 = ((n 0 + 1 : ℕ) : K) := fun n => by push_cast; rfl
  constructor
  · intro n
    rw [map_sub, MvPowerSeries.coeff_pderiv, coeff_product_single_variables (by decide) (by decide),
      PowerSeries.coeff_derivative, Aser_eq, hcast]
    by_cases h : ∃ i j, n 0 + 1 = (p ^ 2) ^ i ∧ n 1 = p * (p ^ 2) ^ j
    · obtain ⟨i, j, hi, hj⟩ := h
      rw [hi, hj, coeff_lgF_pow K hp2, coeff_g0F_of K hp2]
      by_cases hij : i ≤ j
      · rw [coeff_AA_of K hp2 hij ((a0 n).trans hi) ((a1 n).trans hj)]
        have : ((p : K) ^ (i + j + 1))⁻¹ * (((p ^ 2) ^ i : ℕ) : K) -
            ((p : K) ^ i)⁻¹ * (((p ^ 2) ^ i : ℕ) : K) * ((p : K) ^ (j + 1))⁻¹ = 0 := by
          rw [add_assoc, pow_add, mul_inv]
          ring
        rw [this]
        simp
      · have hz : MvPowerSeries.coeff (n + Finsupp.single 0 1) (AA K p 0 1) = 0 := by
          by_contra hne
          obtain ⟨i', j', hij', hi', hj'⟩ := coeff_AA_ne_zero hne
          rw [a0, hi] at hi'
          rw [a1, hj] at hj'
          rw [powq_inj hp2 hi', ppowq_inj hp2 hj'] at hij
          exact hij hij'
        obtain ⟨e, rfl⟩ : ∃ e, i = j + 1 + e := ⟨i - (j + 1), by omega⟩
        have : ((p : K) ^ (j + 1 + e))⁻¹ * (((p ^ 2) ^ (j + 1 + e) : ℕ) : K) *
            ((p : K) ^ (j + 1))⁻¹ = (p : K) ^ e := by
          push_cast
          field_simp
          ring
        rw [hz, zero_mul, zero_sub, norm_neg, this]
        exact norm_p_pow_le_one hp hnp e
    · have hz : MvPowerSeries.coeff (n + Finsupp.single 0 1) (AA K p 0 1) = 0 := by
        by_contra hne
        obtain ⟨i', j', _, hi', hj'⟩ := coeff_AA_ne_zero hne
        exact h ⟨i', j', (a0 n).symm.trans hi', (a1 n).symm.trans hj'⟩
      have hz2 : PowerSeries.coeff (n 0 + 1) (lgF K p) * PowerSeries.coeff (n 1) (g0F K p) = 0 := by
        by_contra hne
        obtain ⟨i', hi'⟩ := coeff_lgF_ne_zero (left_ne_zero_of_mul hne)
        obtain ⟨j', hj'⟩ := coeff_g0F_ne_zero (right_ne_zero_of_mul hne)
        exact h ⟨i', j', hi', hj'⟩
      rw [hz, zero_mul, zero_sub, norm_neg, mul_right_comm, hz2, zero_mul]
      simp
  · intro n
    rw [MvPowerSeries.coeff_pderiv, Aser'_eq, hcast]
    by_cases hne : MvPowerSeries.coeff (n + Finsupp.single 0 1) (AA K p 1 0) = 0
    · rw [hne, zero_mul]
      simp
    obtain ⟨i, j, hij, hi, hj⟩ := coeff_AA_ne_zero hne
    rw [coeff_AA_of K hp2 hij hi hj]
    rw [a0] at hj
    rw [hj]
    obtain ⟨e, rfl⟩ : ∃ e, j = i + e := ⟨j - i, by omega⟩
    have : ((p : K) ^ (i + (i + e) + 1))⁻¹ * ((p * (p ^ 2) ^ (i + e) : ℕ) : K) = (p : K) ^ e := by
      push_cast
      field_simp
      ring
    rw [this]
    exact norm_p_pow_le_one hp hnp e

end Formalism.InvariantFactorPaths.G7
