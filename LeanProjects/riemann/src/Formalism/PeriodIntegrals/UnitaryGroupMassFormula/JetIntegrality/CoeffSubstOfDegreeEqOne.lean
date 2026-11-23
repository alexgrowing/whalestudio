import Mathlib

noncomputable section

namespace PI.JetsPhW.Low

variable {K : Type*} [CommRing K]

theorem coeff_pow_eq_zero {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) :
    ∀ (d : ℕ) (e : σ →₀ ℕ), Finsupp.degree e < d → MvPowerSeries.coeff e (A ^ d) = 0
  | 0, e, h => absurd h (Nat.not_lt_zero _)
  | d + 1, e, h => by
    classical
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hx1 : x.1 = 0
    · rw [hx1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
    · have h1 : 1 ≤ Finsupp.degree x.1 := by
        rw [Nat.one_le_iff_ne_zero]
        intro h0
        exact hx1 ((Finsupp.degree_eq_zero_iff _).1 h0)
      have h2 : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree e := by
        rw [← map_add, hx]
      rw [coeff_pow_eq_zero hA d x.2 (by omega), mul_zero]

theorem const_subst {σ : Type*} {A : MvPowerSeries σ K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst A f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hA)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [map_pow, hA, zero_pow hd, smul_zero]

theorem coeff_subst_low {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries K) {e : σ →₀ ℕ} (he : e ≠ 0)
    (hd : Finsupp.degree e ≤ 2) :
    MvPowerSeries.coeff e (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff e A +
        PowerSeries.coeff 2 f * MvPowerSeries.coeff e (A ^ 2) := by
  classical
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hA)]
  rw [finsum_eq_sum_of_support_subset _ (s := ({1, 2} : Finset ℕ)) ?_]
  · rw [Finset.sum_pair (by norm_num), pow_one, smul_eq_mul, smul_eq_mul]
  · intro d hd'
    rw [Function.mem_support] at hd'
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hc
    push Not at hc
    apply hd'
    rcases Nat.lt_or_ge d 3 with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, MvPowerSeries.coeff_one, if_neg he, smul_zero]
    · rw [coeff_pow_eq_zero hA d e (by omega), smul_zero]

theorem coeff_subst_of_degree_eq_one {σ : Type*} {A : MvPowerSeries σ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (f : PowerSeries K) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff e A := by
  have he : e ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact absurd hd (by norm_num)
  rw [coeff_subst_low hA f he (by omega), coeff_pow_eq_zero hA 2 e (by omega), mul_zero, add_zero]

abbrev E0 : Fin 2 →₀ ℕ := Finsupp.single 0 1
abbrev E1 : Fin 2 →₀ ℕ := Finsupp.single 1 1
abbrev bivariateExponentMonomial : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

theorem degree_expX : Finsupp.degree E0 = 1 := Finsupp.degree_single _ _
theorem degree_expY : Finsupp.degree E1 = 1 := Finsupp.degree_single _ _
theorem degree_expXY : Finsupp.degree bivariateExponentMonomial = 2 := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem expXY_ne_zero : bivariateExponentMonomial ≠ 0 := by
  intro h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simp at this

theorem expX_ne_expY : E0 ≠ E1 := by
  intro h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simp at this

theorem eq_of_add_eq_expXY {x y : Fin 2 →₀ ℕ} (hxy : x + y = bivariateExponentMonomial) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x = E0 ∧ y = E1) ∨ (x = E1 ∧ y = E0) := by
  have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hxy
  have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) hxy
  simp only [Finsupp.add_apply, Finsupp.single_apply] at h0 h1
  norm_num at h0 h1
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (Finsupp.ext (fun i => by fin_cases i <;> simp [hc.1, hc.2]))
  have hy' : y 0 ≠ 0 ∨ y 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (Finsupp.ext (fun i => by fin_cases i <;> simp [hc.1, hc.2]))
  rcases Nat.eq_zero_or_pos (x 0) with a0 | a0
  · right
    refine ⟨Finsupp.ext (fun i => ?_), Finsupp.ext (fun i => ?_)⟩ <;> fin_cases i <;>
      simp <;> omega
  · left
    refine ⟨Finsupp.ext (fun i => ?_), Finsupp.ext (fun i => ?_)⟩ <;> fin_cases i <;>
      simp <;> omega

theorem coeff_expXY_mul {A B : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.coeff bivariateExponentMonomial (A * B) =
      MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B +
        MvPowerSeries.coeff E1 A * MvPowerSeries.coeff E0 B := by
  classical
  rw [MvPowerSeries.coeff_mul]
  have hsub : ({(E0, E1), (E1, E0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) ⊆
      Finset.HasAntidiagonal.antidiagonal bivariateExponentMonomial := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rcases hq with rfl | rfl
    · rfl
    · exact add_comm _ _
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_pair (fun h => expX_ne_expY (congrArg Prod.fst h))]
  · intro q hq hq'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    by_cases h1 : q.1 = 0
    · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA, zero_mul]
    by_cases h2 : q.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB, mul_zero]
    exfalso
    apply hq'
    rcases eq_of_add_eq_expXY hq h1 h2 with ⟨a, b⟩ | ⟨a, b⟩
    · simp [Prod.ext_iff, a, b]
    · simp [Prod.ext_iff, a, b]

theorem coeff_expX_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff E0 (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff E0 A :=
  coeff_subst_of_degree_eq_one hA f degree_expX

theorem coeff_expY_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff E1 (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff E1 A :=
  coeff_subst_of_degree_eq_one hA f degree_expY

theorem coeff_expXY_subst {A : MvPowerSeries (Fin 2) K} (hA : MvPowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    MvPowerSeries.coeff bivariateExponentMonomial (PowerSeries.subst A f) =
      PowerSeries.coeff 1 f * MvPowerSeries.coeff bivariateExponentMonomial A +
        PowerSeries.coeff 2 f *
          (2 * (MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 A)) := by
  rw [coeff_subst_low hA f expXY_ne_zero (by rw [degree_expXY]), pow_two, coeff_expXY_mul hA hA]
  ring

theorem pcoeff1_subst {A : PowerSeries K} (hA : PowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    PowerSeries.coeff 1 (PowerSeries.subst A f : PowerSeries K) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 A :=
  coeff_subst_of_degree_eq_one (σ := Unit) hA f (Finsupp.degree_single _ _)

theorem pcoeff2_subst {A : PowerSeries K} (hA : PowerSeries.constantCoeff A = 0)
    (f : PowerSeries K) :
    PowerSeries.coeff 2 (PowerSeries.subst A f : PowerSeries K) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 2 A +
        PowerSeries.coeff 2 f * (PowerSeries.coeff 1 A) ^ 2 := by
  have h := coeff_subst_low (σ := Unit) hA f (e := Finsupp.single () 2)
    (by simp) (by rw [Finsupp.degree_single])
  have h2 : PowerSeries.coeff 2 (A ^ 2) = (PowerSeries.coeff 1 A) ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [hA]
    ring
  rw [← h2]
  exact h

end PI.JetsPhW.Low
