import Mathlib
import Formalism.PeriodIntegrals.FglGram

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram

open PI.FglGram MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem intP_add {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x + y) :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem valuation_coeff_mul_nonneg {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x * y) := by
  show ‖x * y‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_mul hx hy (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem isIntegralAt_neg {x : ℂ_[p]} (hx : IsIntP x) : IsIntP (-x) := by
  show ‖-x‖ ≤ 1
  rw [norm_neg]
  exact hx

theorem intP_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ_[p]) (h : ∀ i ∈ s, IsIntP (f i)) :
    IsIntP (∑ i ∈ s, f i) := by
  revert h
  refine Finset.induction_on s (fun _ => by simp [IsIntP]) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha]
  exact intP_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem int_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := fun n => by
  rw [MvPowerSeries.coeff_mul]
  exact intP_sum _ _ fun x _ => valuation_coeff_mul_nonneg (hF _) (hG _)

theorem int_one : IntegralMv (1 : MvPowerSeries σ ℂ_[p]) := fun n => by
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp [IsIntP]

private lemma low_mul_lemma {X Y : MvPowerSeries σ ℂ_[p]} {a b : ℕ}
    (hX : ∀ β : σ →₀ ℕ, β.degree < a → coeff β X = 0) (hY : ∀ β : σ →₀ ℕ, β.degree < b → coeff β Y = 0) :
    ∀ β : σ →₀ ℕ, β.degree < a + b → coeff β (X * Y) = 0 := by
  intro β hβ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hd : x.1.degree + x.2.degree = β.degree := by rw [← hx, map_add]
  by_cases h1 : x.1.degree < a
  · rw [hX _ h1, zero_mul]
  · rw [hY _ (by omega), mul_zero]

private lemma low_pow_lemma_2 {u : MvPowerSeries σ ℂ_[p]} (hu : constantCoeff u = 0) (n : ℕ) :
    ∀ β : σ →₀ ℕ, β.degree < n → coeff β (u ^ n) = 0 := by
  induction n with
  | zero => intro β h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ]
    refine low_mul_lemma ih fun β hβ => ?_
    have h0 : β = 0 := (Finsupp.degree_eq_zero_iff β).mp (by omega)
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hu]

theorem coeff_mul_pow_eq_zero {u : MvPowerSeries σ ℂ_[p]} (hu : constantCoeff u = 0)
    (W : MvPowerSeries σ ℂ_[p]) {n : ℕ} {α : σ →₀ ℕ} (h : α.degree < n) :
    coeff α (W * u ^ n) = 0 := by
  have hW : ∀ β : σ →₀ ℕ, β.degree < 0 → coeff β W = 0 := fun β h => absurd h (Nat.not_lt_zero _)
  have := low_mul_lemma hW (low_pow_lemma_2 hu n) α (by omega)
  exact this

theorem coeff_pow_mul_pow_eq_zero {D E : MvPowerSeries σ ℂ_[p]} (hD : constantCoeff D = 0)
    (hE : constantCoeff E = 0) {i j : ℕ} {α : σ →₀ ℕ} (h : α.degree < i + j) :
    coeff α (D ^ i * E ^ j) = 0 :=
  low_mul_lemma (low_pow_lemma_2 hD i) (low_pow_lemma_2 hE j) α h

theorem coeff_expMv (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv F) =
      ∑ n ∈ Finset.range (α.degree + 1), coeff α (F ^ n) / (n.factorial : ℂ_[p]) := rfl

theorem coeff_expMv_of_le {F : MvPowerSeries σ ℂ_[p]} (hF : constantCoeff F = 0) {α : σ →₀ ℕ}
    (N : ℕ) (hN : α.degree ≤ N) :
    coeff α (expMv F) = ∑ n ∈ Finset.range (N + 1), coeff α (F ^ n) / (n.factorial : ℂ_[p]) := by
  rw [coeff_expMv]
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [low_pow_lemma_2 hF n α (by omega), zero_div]

theorem reindex {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → ℕ → M)
    (hg : ∀ i j, N < i + j → g i j = 0) :
    ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (n + 1), g m (n - m) =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), g i j := by
  have key := Finset.sum_Ico_Ico_comm 0 (N + 1) (fun m n => g m (n - m))
  simp only [Finset.range_eq_Ico]
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  have e : ∑ j ∈ Finset.Ico i (N + 1), g i (j - i) = ∑ j ∈ Finset.range (N + 1 - i), g i j := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
  rw [e, ← Finset.range_eq_Ico]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    exact hg i j (by omega)

theorem expMv_add {D E : MvPowerSeries σ ℂ_[p]} (hD : constantCoeff D = 0) (hE : constantCoeff E = 0) :
    expMv (D + E) = expMv D * expMv E := by
  ext α
  have hR : coeff α (expMv D * expMv E) = ∑ i ∈ Finset.range (α.degree + 1), ∑ j ∈ Finset.range (α.degree + 1),
      coeff α (D ^ i * E ^ j) / ((i.factorial : ℂ_[p]) * (j.factorial : ℂ_[p])) := by
    rw [MvPowerSeries.coeff_mul]
    have step : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal α, coeff x.1 (expMv D) * coeff x.2 (expMv E) =
        ∑ i ∈ Finset.range (α.degree + 1), ∑ j ∈ Finset.range (α.degree + 1),
          coeff x.1 (D ^ i) * coeff x.2 (E ^ j) / ((i.factorial : ℂ_[p]) * (j.factorial : ℂ_[p])) := by
      intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hdeg : x.1.degree + x.2.degree = α.degree := by rw [← hx, map_add]
      rw [coeff_expMv_of_le hD α.degree (by omega), coeff_expMv_of_le hE α.degree (by omega),
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [div_mul_div_comm]
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.coeff_mul, Finset.sum_div]
  have hL : coeff α (expMv (D + E)) = ∑ n ∈ Finset.range (α.degree + 1), ∑ m ∈ Finset.range (n + 1),
      coeff α (D ^ m * E ^ (n - m)) / ((m.factorial : ℂ_[p]) * ((n - m).factorial : ℂ_[p])) := by
    rw [coeff_expMv]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_pow, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [mul_comm _ ((n.choose m : ℕ) : MvPowerSeries σ ℂ_[p]), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    have hc : ((n.choose m : ℕ) : ℂ_[p]) * (m.factorial : ℂ_[p]) * ((n - m).factorial : ℂ_[p]) =
        (n.factorial : ℂ_[p]) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmn
    have h1 : ((n.choose m : ℕ) : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hmn).ne'
    rw [← hc, mul_assoc, mul_div_mul_left _ _ h1]
  rw [hL, hR]
  exact reindex _ (fun i j => coeff α (D ^ i * E ^ j) / ((i.factorial : ℂ_[p]) * (j.factorial : ℂ_[p])))
    (fun i j hij => by rw [coeff_pow_mul_pow_eq_zero hD hE hij, zero_div])

theorem expMv_zero : expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by
  ext α
  rw [coeff_expMv, Finset.sum_eq_single 0]
  · simp
  · intro n _ hn
    rw [zero_pow hn, map_zero, zero_div]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem constantCoeff_expMv (F : MvPowerSeries σ ℂ_[p]) : constantCoeff (expMv F) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expMv]
  simp

theorem int_expMv_neg {D : MvPowerSeries σ ℂ_[p]} (hD : constantCoeff D = 0)
    (h : IntegralMv (expMv D)) : IntegralMv (expMv (-D)) := by
  have hnD : constantCoeff (-D) = 0 := by rw [map_neg, hD, neg_zero]
  have hX : expMv (-D) * expMv D = 1 := by rw [← expMv_add hnD hD, neg_add_cancel, expMv_zero]
  have hU0 : coeff 0 (expMv D) = 1 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_expMv]
  suffices H : ∀ n, ∀ α : σ →₀ ℕ, α.degree < n → IsIntP (coeff α (expMv (-D))) from
    fun α => H _ α (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro α hα; exact absurd hα (Nat.not_lt_zero _)
  | succ n ih =>
    intro α hα
    have e := congrArg (coeff α) hX
    have hmem : (α, (0 : σ →₀ ℕ)) ∈ Finset.HasAntidiagonal.antidiagonal α := by simp
    rw [MvPowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem, hU0, mul_one] at e
    rw [eq_sub_of_add_eq e, sub_eq_add_neg]
    refine intP_add (int_one α) (isIntegralAt_neg (intP_sum _ _ fun x hx => valuation_coeff_mul_nonneg (ih x.1 ?_) (h x.2)))
    have hx' := Finset.mem_erase.mp hx
    have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx'.2
    have h2 : x.2 ≠ 0 := by
      intro h0
      apply hx'.1
      exact Prod.ext (by rw [← h1, h0, add_zero]) h0
    have h3 : x.2.degree ≠ 0 := fun hd => h2 ((Finsupp.degree_eq_zero_iff _).mp hd)
    have h4 : x.1.degree + x.2.degree = α.degree := by rw [← h1, map_add]
    omega

def Good (D : MvPowerSeries σ ℂ_[p]) : Prop :=
  constantCoeff D = 0 ∧ IntegralMv (expMv D)

theorem simeq_iff_good (f g : MvPowerSeries σ ℂ_[p]) : Simeq f g ↔ Good (f - g) := Iff.rfl

theorem good_add {D E : MvPowerSeries σ ℂ_[p]} (hD : Good D) (hE : Good E) : Good (D + E) := by
  refine ⟨by rw [map_add, hD.1, hE.1, add_zero], ?_⟩
  rw [expMv_add hD.1 hE.1]
  exact int_mul hD.2 hE.2

theorem good_neg {D : MvPowerSeries σ ℂ_[p]} (hD : Good D) : Good (-D) :=
  ⟨by rw [map_neg, hD.1, neg_zero], int_expMv_neg hD.1 hD.2⟩

theorem good_sub {D E : MvPowerSeries σ ℂ_[p]} (hD : Good D) (hE : Good E) : Good (D - E) := by
  rw [sub_eq_add_neg]
  exact good_add hD (good_neg hE)

end PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram
