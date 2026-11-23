import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensSt

noncomputable section

namespace PI.VolStabW

open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors

namespace LocalCountingSum

variable (K : Type) [Field K] [NumberField K]

def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

theorem sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  classical
  simp only [cnt, ← Nat.cast_sum]
  congr 1
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp only [sum_cnt, Real.rpow_one]
  have ht := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, Nat.cast_le] at ht
  refine isBigO_of_div_tendsto_nhds
    (f := fun n : ℕ ↦ (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ))
    (g := fun n : ℕ ↦ (n : ℝ)) ?_ _ ht
  filter_upwards [eventually_ne_atTop 0] with n hn h
  exact absurd h (by exact_mod_cast hn)

theorem cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have hL := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := 2) (sum_cnt_bigO K)
    (fun n ↦ by unfold cnt; positivity) zero_le_one (by norm_num)
  refine hL.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold cnt; positivity)]
    norm_num

end LocalCountingSum

theorem qV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem qvSum_holds : QvSum := by
  intro F _ _
  classical
  have hc := LocalCountingSum.cnt_summable F
  refine summable_of_sum_le (c := ∑' n, LocalCountingSum.cnt F n / (n : ℝ) ^ 2)
    (fun v ↦ by simp only [Pi.zero_apply]; positivity) fun S ↦ ?_
  let N : HeightOneSpectrum (𝓞 F) → ℕ := fun v ↦ Ideal.absNorm v.asIdeal
  have e1 : ∑ v ∈ S, (qV v)⁻¹ ^ 2 = ∑ v ∈ S, ((N v : ℝ))⁻¹ ^ 2 :=
    Finset.sum_congr rfl fun v _ ↦ by rw [qV_eq]
  rw [e1, Finset.sum_comp (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 2) N]
  have hcard : ∀ n, ((S.filter fun v ↦ N v = n).card : ℝ) ≤ LocalCountingSum.cnt F n := by
    intro n
    unfold LocalCountingSum.cnt
    have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    have hinj : Function.Injective
        (fun v : (S.filter fun v ↦ N v = n) ↦
          (⟨v.1.asIdeal, (Finset.mem_filter.mp v.2).2⟩ :
            {I : Ideal (𝓞 F) // Ideal.absNorm I = n})) := by
      intro x y h
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      exact congrArg Subtype.val h
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
    exact_mod_cast this
  calc ∑ n ∈ S.image N, (S.filter fun v ↦ N v = n).card • ((n : ℝ))⁻¹ ^ 2
      ≤ ∑ n ∈ S.image N, LocalCountingSum.cnt F n / (n : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun n _ ↦ ?_
        rw [nsmul_eq_mul, div_eq_mul_inv, inv_pow]
        exact mul_le_mul_of_nonneg_right (hcard n) (by positivity)
    _ ≤ ∑' n, LocalCountingSum.cnt F n / (n : ℝ) ^ 2 :=
        hc.sum_le_tsum _ fun n _ ↦ by unfold LocalCountingSum.cnt; positivity

end PI.VolStabW
