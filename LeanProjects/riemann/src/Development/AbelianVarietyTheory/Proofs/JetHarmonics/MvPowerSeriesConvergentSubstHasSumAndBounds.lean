import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.SubstSum

variable {K : Type} [NormedField K] [IsUltrametricDist K] {τ : Type}

def Decay (θ : ℝ) (m : ℕ) (S : MvPowerSeries τ K) : Prop :=
  ∀ μ : τ →₀ ℕ, ‖MvPowerSeries.coeff μ S‖ ≤ θ ^ (m - μ.degree)

omit [IsUltrametricDist K] in
theorem decay_one (θ : ℝ) : Decay θ 0 (1 : MvPowerSeries τ K) := by
  classical
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem Decay.mul {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {m n : ℕ} {S T : MvPowerSeries τ K}
    (hS : Decay θ m S) (hT : Decay θ n T) : Decay θ (m + n) (S * T) := by
  classical
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg h0 _) fun p hp => ?_
  have hp' : p.1 + p.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 S‖ * ‖MvPowerSeries.coeff p.2 T‖
      ≤ θ ^ (m - p.1.degree) * θ ^ (n - p.2.degree) :=
        mul_le_mul (hS _) (hT _) (norm_nonneg _) (pow_nonneg h0 _)
    _ = θ ^ ((m - p.1.degree) + (n - p.2.degree)) := (pow_add _ _ _).symm
    _ ≤ θ ^ (m + n - μ.degree) := by
        apply pow_le_pow_of_le_one h0 h1
        rw [← hp', map_add]
        omega

theorem Decay.pow {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {S : MvPowerSeries τ K}
    (hS : Decay θ 1 S) (n : ℕ) : Decay θ n (S ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact decay_one θ
  | succ n ih => rw [pow_succ]; exact ih.mul h0 h1 hS

theorem decay_prod {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {σ : Type} (t : Finset σ)
    (s : σ → MvPowerSeries τ K) (hs : ∀ i, Decay θ 1 (s i)) (ν : σ → ℕ) :
    Decay θ (∑ i ∈ t, ν i) (∏ i ∈ t, s i ^ ν i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty]
    exact decay_one θ
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (Decay.pow h0 h1 (hs a) (ν a)).mul h0 h1 ih

omit [IsUltrametricDist K] in
theorem decay_of_small {θ : ℝ} {S : MvPowerSeries τ K} (hS : Intg S)
    (hθ : ‖MvPowerSeries.constantCoeff S‖ ≤ θ) : Decay θ 1 S := by
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    rw [map_zero, Nat.sub_zero, pow_one, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hθ
  · have hd : μ.degree ≠ 0 := (Finsupp.degree_eq_zero_iff μ).not.2 hμ
    have : 1 - μ.degree = 0 := by omega
    rw [this, pow_zero]
    exact hS μ

theorem exists_decay {σ : Type} [Fintype σ] (s : σ → MvPowerSeries τ K) (hs : ∀ i, Small (s i)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ (ν : σ →₀ ℕ) (μ : τ →₀ ℕ),
      ‖MvPowerSeries.coeff μ (∏ i, s i ^ ν i)‖ ≤ θ ^ (ν.degree - μ.degree) := by
  classical
  set θ : ℝ := ((Finset.univ.sup fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊ : NNReal) : ℝ)
    with hθdef
  have hsi : ∀ i, Intg (s i) ∧ ‖MvPowerSeries.constantCoeff (s i)‖ < 1 := hs
  have h0 : 0 ≤ θ := NNReal.coe_nonneg _
  have hlt : θ < 1 := by
    have : (Finset.univ.sup fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊) < 1 :=
      (Finset.sup_lt_iff (by simp)).2 fun i _ => by
        have h := (hsi i).2
        rw [← coe_nnnorm] at h
        exact_mod_cast h
    exact_mod_cast this
  have hle : ∀ i, ‖MvPowerSeries.constantCoeff (s i)‖ ≤ θ := fun i => by
    rw [hθdef, ← coe_nnnorm]
    exact_mod_cast Finset.le_sup (f := fun i => ‖MvPowerSeries.constantCoeff (s i)‖₊)
      (Finset.mem_univ i)
  refine ⟨θ, h0, hlt, fun ν μ => ?_⟩
  have h := decay_prod h0 hlt.le Finset.univ s (fun i => decay_of_small (hsi i).1 (hle i)) ν μ
  rwa [← Finsupp.degree_eq_sum] at h

theorem tendsto_degree {σ : Type} [Fintype σ] :
    Filter.Tendsto (fun ν : σ →₀ ℕ => ν.degree) Filter.cofinite Filter.atTop := by
  classical
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (0 : σ →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun _ => b)).subset
    fun ν hν => ?_
  simp only [Set.mem_ofPred_eq, not_le] at hν
  refine Set.mem_Icc.2 ⟨zero_le, Finsupp.le_def.2 fun i => ?_⟩
  simpa using (Finsupp.le_degree i ν).trans hν.le

end GlobalTheory.ConvSer.SubstSum

open GlobalTheory.ConvSer.SubstSum in

theorem GlobalTheory.ConvSer.csub_hasSum_and_bounds :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, Small (s i)) → Bdd S → (∀ μ, HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)) (MvPowerSeries.coeff μ (csub s S))) ∧ Bdd (csub s S) ∧ (Intg S → Intg (csub s S)) ∧ (Intg S → MvPowerSeries.constantCoeff S = 0 → Small (csub s S)) := by
  intro K _ _ _ σ τ _ s S hs hS
  obtain ⟨θ, h0, h1, hθ⟩ := exists_decay s hs
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ C := hS
  set t : (τ →₀ ℕ) → (σ →₀ ℕ) → K := fun μ ν =>
    MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i) with ht
  have hprod1 : ∀ (ν : σ →₀ ℕ) μ, ‖MvPowerSeries.coeff μ (∏ i, s i ^ ν i)‖ ≤ 1 := fun ν μ =>
    (hθ ν μ).trans (pow_le_one₀ h0 h1.le)
  have hsum : ∀ μ, HasSum (t μ) (MvPowerSeries.coeff μ (csub s S)) := by
    intro μ
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    have htend : Filter.Tendsto (t μ) Filter.cofinite (nhds 0) := by
      refine squeeze_zero_norm (a := fun ν => max C 0 * θ ^ (ν.degree - μ.degree))
        (fun ν => ?_) ?_
      · rw [ht, norm_mul]
        exact mul_le_mul ((hC ν).trans (le_max_left _ _)) (hθ ν μ) (norm_nonneg _) hC0
      · have h : Filter.Tendsto (fun ν : σ →₀ ℕ => θ ^ (ν.degree - μ.degree))
            Filter.cofinite (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
            ((Filter.tendsto_sub_atTop_nat μ.degree).comp tendsto_degree)
        simpa using h.const_mul (max C 0)
    have heq : MvPowerSeries.coeff μ (csub s S) = ∑' ν, t μ ν := rfl
    rw [heq]
    exact (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero htend).hasSum
  have hbound : ∀ B : ℝ, 0 ≤ B → (∀ μ ν, ‖t μ ν‖ ≤ B) →
      ∀ μ, ‖MvPowerSeries.coeff μ (csub s S)‖ ≤ B := fun B hB h μ => by
    rw [← (hsum μ).tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB (h μ)
  have hterm : ∀ μ ν, ‖t μ ν‖ ≤ ‖MvPowerSeries.coeff ν S‖ := fun μ ν => by
    rw [ht, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hprod1 ν μ)
  have hintg : Intg S → Intg (csub s S) := fun hI =>
    hbound 1 zero_le_one fun μ ν => (hterm μ ν).trans (hI ν)
  refine ⟨hsum, ?_, hintg, fun hI h00 => ?_⟩
  · exact Exists.intro (max C 0) (hbound _ (le_max_right _ _) fun μ ν =>
      (hterm μ ν).trans ((hC ν).trans (le_max_left _ _)))
  · have hc : ‖MvPowerSeries.coeff 0 (csub s S)‖ ≤ θ := by
      rw [← (hsum 0).tsum_eq]
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg h0 fun ν => ?_
      by_cases hν : ν = 0
      · subst hν
        simp [ht, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h00, h0]
      · rw [ht, norm_mul]
        have hd : 1 ≤ ν.degree - (0 : τ →₀ ℕ).degree := by
          have a := (Finsupp.degree_eq_zero_iff ν).not.2 hν
          rw [map_zero]
          omega
        calc ‖MvPowerSeries.coeff ν S‖ * ‖MvPowerSeries.coeff 0 (∏ i, s i ^ ν i)‖
            ≤ 1 * θ := mul_le_mul (hI ν)
              ((hθ ν 0).trans ((pow_le_pow_of_le_one h0 h1.le hd).trans_eq (pow_one θ)))
              (norm_nonneg _) zero_le_one
          _ = θ := one_mul θ
    exact And.intro (hintg hI)
      (by rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hc.trans_lt h1)
