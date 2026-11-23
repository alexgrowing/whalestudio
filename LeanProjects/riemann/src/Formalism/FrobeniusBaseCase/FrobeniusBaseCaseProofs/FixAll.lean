import Formalism.FrobeniusBaseCase.StatementFix
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.BaseCaseFalseGeneralHolds

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

namespace Data

variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

theorem qs_sigma_lt_one (s : ℕ) (hsK : s < D.K) : qnum D.l ^ s * sg D.l D.i < 1 := by
  have hl : (3 : ℝ) ≤ (D.l : ℝ) := by exact_mod_cast D.l_ge
  have h1 := identity_twenty_d D.l D.i (by have := D.l_ge; omega) D.i_odd
  have hq1 : (1 : ℝ) ≤ qnum D.l := by unfold qnum; nlinarith
  have hsg : 0 < sg D.l D.i := by unfold sg; positivity
  have h2 : qnum D.l ^ (s + 1) ≤ qnum D.l ^ Kn D.i := pow_le_pow_right₀ hq1 hsK
  have h3 : qnum D.l ^ (s + 1) * sg D.l D.i ≤ 3 * (D.l : ℝ) / 8 := by
    rw [← h1]; exact mul_le_mul_of_nonneg_right h2 hsg.le
  by_contra hcon
  rw [not_lt] at hcon
  have h4 : qnum D.l ^ (s + 1) * sg D.l D.i = (qnum D.l ^ s * sg D.l D.i) * qnum D.l := by
    rw [pow_succ]; ring
  rw [h4] at h3
  have h5 : qnum D.l ≤ (qnum D.l ^ s * sg D.l D.i) * qnum D.l := by nlinarith
  unfold qnum at h5 h3
  nlinarith

theorem e_real (s : ℕ) : qnum D.l ^ s * rho D.l - (eNum D.l s : ℝ) = rho D.l := by
  have h := (identity_e D.l s (by have := D.l_ge; omega)).2.2
  have hl1 : 1 ≤ D.l ^ 2 := Nat.one_le_pow _ _ D.l_prime.pos
  have hR : (eNum D.l s : ℝ) * ((D.l : ℝ) ^ 2 - 1) + 1 = ((D.l : ℝ) ^ 2) ^ s := by
    have h' : ((eNum D.l s * (D.l ^ 2 - 1) + 1 : ℕ) : ℝ) = (((D.l ^ 2) ^ s : ℕ) : ℝ) := by rw [h]
    push_cast [Nat.cast_sub hl1] at h'
    exact h'
  have hm := rho_mul D.l_ge
  unfold qnum
  rw [← hR]
  linear_combination (eNum D.l s : ℝ) * hm

theorem unit_entry_all : D.UnitEntryAll := by
  intro s hs1 hsK c hc P hP d hu h
  have h1 := h.1 c (by rw [hc]; exact hsK)
  rw [hc, D.zvec_eq_zero (by omega), zero_sub] at h1
  have h2 := h1 (Finsupp.single d (D.q ^ s))
  have hq0 : D.q ^ s ≠ 0 := pow_ne_zero _ (by have := D.q_pos; omega)
  have hcoef : coeff (Finsupp.single d (D.q ^ s)) (D.m s c)
      = ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) * P d := by
    rw [hP, coeff_C_mul, coeff_sum_C_mul_X_pow]
    simp only [Finsupp.single_left_inj hq0]
    rw [Finset.sum_ite_eq]
    simp
  have hvl : D.v (((D.l : k) ^ eNum D.l s)⁻¹) = ((-(eNum D.l s : ℝ) : ℝ) : WithTop ℝ) := by
    rw [← inv_pow]
    generalize eNum D.l s = e
    induction e with
    | zero => simp
    | succ e ih =>
      rw [pow_succ, AddValuation.map_mul, ih, D.v_l_inv, ← WithTop.coe_add]
      congr 1
      push_cast
      ring
  have hsign : D.v ((-1 : k) ^ s) = 0 := by
    rcases neg_one_pow_eq_or k s with h | h <;> rw [h] <;> simp [AddValuation.map_neg]
  rw [map_neg, AddValuation.map_neg, hcoef, AddValuation.map_mul, AddValuation.map_mul, hsign, hvl,
    hu, zero_add, add_zero, Finsupp.degree_single, ← WithTop.coe_add, WithTop.coe_le_coe] at h2
  have h3 := D.qs_sigma_lt_one s hsK
  have h4 := D.e_real s
  have h5 : ((D.q ^ s : ℕ) : ℝ) = qnum D.l ^ s := by
    rw [Nat.cast_pow, D.q_cast]
  rw [h5] at h2
  unfold Data.top Data.rad at h2
  nlinarith

theorem start_eq_z : D.StartEqZ := by
  intro hm
  funext c
  unfold start
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (D.lev c) with h0 | h0
    · rw [h0]; rfl
    · rw [hm (D.lev c) c h0 h rfl, D.zvec_eq_zero (by omega)]
  · rw [D.zvec_eq_zero (by have := D.K_pos; omega)]

theorem coeff_logSum (t : C → MvPowerSeries Z k) (b : C) (A : Z →₀ ℕ) (N : ℕ) :
    coeff A (∑ c, ∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j)) =
      ∑ c, ∑ j ∈ Finset.Icc 1 N, D.al c j b * coeff A (t c ^ (D.l ^ j)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => coeff_C_mul _ _ _

theorem LogIffFix_statement : D.LogIffFix := by
  intro t ht
  constructor
  · intro h
    funext b
    ext A
    rw [D.opIsLimit t ht b A A.degree le_rfl, coeff_PsiPartial]
    have := h b A A.degree le_rfl
    rw [map_add, coeff_logSum] at this
    linear_combination -this
  · intro h b A N hN
    have := D.opIsLimit t ht b A N hN
    rw [h, coeff_PsiPartial] at this
    rw [map_add, coeff_logSum]
    linear_combination this

theorem log_unique_bis : D.LogUnique := by
  obtain ⟨t, ⟨h0, h1⟩, huniq⟩ := D.hasUniqueFixedPoint.1
  exact ⟨t, ⟨h0, (D.LogIffFix_statement t h0).2 h1⟩,
    fun t' ht' => huniq t' ⟨ht'.1, (D.LogIffFix_statement t' ht'.1).1 ht'.2⟩⟩

theorem chain_ii_of_log : D.ChainIILog :=
  fun t h0 h1 => D.chainII_holds t h0 ((D.LogIffFix_statement t h0).1 h1)

end Data

end

end Formalism.BaseCaseIdentities
