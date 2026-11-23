import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SummableSqGeom

open Filter Topology Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {ι X : Type*} {q : ι → ℝ}

theorem prod_dif_eq_zero {R : ι → ℕ → ℝ} {v : ι →₀ ℕ} {i : ι} (hi : i ∈ v.support)
    (hR : ∀ j, R i j = 1) : v.prod (dif R) = 0 := by
  unfold Finsupp.prod
  refine Finset.prod_eq_zero hi ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  rw [hk]
  show R i (k + 1) - R i k = 0
  rw [hR, hR, sub_self]

open scoped Classical in
theorem sum_eq_tsum {R : ι → ℕ → ℝ} (hR0 : ∀ i, R i 0 = 1) (val : X → ι →₀ ℕ) (B : Finset X)
    (a : X → ℝ) (sc : ℝ) :
    sc * ∑ n ∈ B, a n * (val n).prod R =
      ∑' v : ι →₀ ℕ, v.prod (dif R) * (sc * ∑ n ∈ B.filter (fun n => v ≤ val n), a n) := by
  set T : Finset (ι →₀ ℕ) := B.biUnion fun n => ebox (val n).support (val n) with hT
  have hfil : ∀ n ∈ B, T.filter (fun v => v ≤ val n) = ebox (val n).support (val n) := by
    intro n hn
    ext v
    rw [Finset.mem_filter, mem_ebox_support]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Finset.mem_biUnion.mpr ⟨n, hn, mem_ebox_support.mpr h⟩, h⟩
  have hzero : ∀ v ∉ T,
      v.prod (dif R) * (sc * ∑ n ∈ B.filter (fun n => v ≤ val n), a n) = 0 := by
    intro v hv
    have hE : B.filter (fun n => v ≤ val n) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro n hn hle
      exact hv (Finset.mem_biUnion.mpr ⟨n, hn, mem_ebox_support.mpr hle⟩)
    rw [hE, Finset.sum_empty, mul_zero, mul_zero]
  have lhs : sc * ∑ n ∈ B, a n * (val n).prod R =
      ∑ v ∈ T, ∑ n ∈ B, if v ≤ val n then v.prod (dif R) * (sc * a n) else 0 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [prod_eq_sum_dif R hR0 (val n), ← hfil n hn, Finset.sum_filter, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  have rhs : ∀ v : ι →₀ ℕ,
      v.prod (dif R) * (sc * ∑ n ∈ B.filter (fun n => v ≤ val n), a n) =
        ∑ n ∈ B, if v ≤ val n then v.prod (dif R) * (sc * a n) else 0 := by
    intro v
    rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  rw [lhs, (hasSum_sum_of_ne_finset_zero hzero).tsum_eq]
  exact Finset.sum_congr rfl fun v _ => (rhs v).symm

open scoped Classical in
theorem tendsto_weighted (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹)
    (S : Finset ι) {R : ι → ℕ → ℝ} (hR0 : ∀ i, R i 0 = 1) (hRS : ∀ i ∈ S, ∀ j, R i j = 1)
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i)
    (val : X → ι →₀ ℕ) (B : ℕ → Finset X) (a : X → ℝ) (sc : ℕ → ℝ) (c C : ℝ)
    (H1 : ∀ v : ι →₀ ℕ, Disjoint v.support S →
      Tendsto (fun j => sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) atTop
        (𝓝 (c / nrm q v)))
    (H2 : ∀ᶠ j in atTop, ∀ v : ι →₀ ℕ,
      |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n| ≤ C / nrm q v) :
    Tendsto (fun j => sc j * ∑ n ∈ B j, a n * (val n).prod R) atTop
      (𝓝 (c * ∑' v : ι →₀ ℕ, v.prod (dif R) / nrm q v)) := by
  have hlim : Tendsto (fun j => ∑' v : ι →₀ ℕ,
      v.prod (dif R) * (sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n)) atTop
      (𝓝 (∑' v : ι →₀ ℕ, v.prod (dif R) * (c / nrm q v))) := by
    refine tendsto_tsum_of_dominated_convergence
      (f := fun j v => v.prod (dif R) * (sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n))
      (g := fun v => v.prod (dif R) * (c / nrm q v))
      (bound := fun v => C * (|v.prod (dif R)| / nrm q v))
      ((summable_dif hq hsum hRb).mul_left C) ?_ ?_
    · intro v
      try dsimp only
      by_cases hv : Disjoint v.support S
      · exact (H1 v hv).const_mul _
      · obtain ⟨i, hiv, hiS⟩ := Finset.not_disjoint_iff.mp hv
        have h0 : v.prod (dif R) = 0 := prod_dif_eq_zero hiv (hRS i hiS)
        simp only [h0, zero_mul]
        exact tendsto_const_nhds
    · filter_upwards [H2] with j hj v
      try dsimp only
      rw [Real.norm_eq_abs, abs_mul]
      calc |v.prod (dif R)| * |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n|
          ≤ |v.prod (dif R)| * (C / nrm q v) :=
            mul_le_mul_of_nonneg_left (hj v) (abs_nonneg _)
        _ = C * (|v.prod (dif R)| / nrm q v) := by ring
  have heq : ∀ j, ∑' v : ι →₀ ℕ,
      v.prod (dif R) * (sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) =
        sc j * ∑ n ∈ B j, a n * (val n).prod R :=
    fun j => (sum_eq_tsum hR0 val (B j) a (sc j)).symm
  have hcl : ∑' v : ι →₀ ℕ, v.prod (dif R) * (c / nrm q v) =
      c * ∑' v : ι →₀ ℕ, v.prod (dif R) / nrm q v := by
    rw [← tsum_mul_left]
    refine tsum_congr fun v => ?_
    ring
  rw [← hcl]
  exact Tendsto.congr heq hlim

open scoped Classical in

def cut (ρ : ι → ℕ → ℝ) (S' : Finset ι) (i : ι) (j : ℕ) : ℝ := if i ∈ S' then ρ i j else 1

theorem prod_cut {ρ : ι → ℕ → ℝ} (hρ0 : ∀ i, ρ i 0 = 1) (S' : Finset ι) (w : ι →₀ ℕ) :
    w.prod (cut ρ S') = ∏ i ∈ S', ρ i (w i) := by
  classical
  have hg : ∀ i ∈ w.support ∪ S', cut ρ S' i 0 = 1 := fun i _ => by simp [cut, hρ0]
  rw [Finsupp.prod_of_support_subset w (s := w.support ∪ S') Finset.subset_union_left
    (cut ρ S') hg]
  symm
  calc ∏ i ∈ S', ρ i (w i) = ∏ i ∈ S', cut ρ S' i (w i) :=
        Finset.prod_congr rfl fun i hi => by simp [cut, hi]
    _ = ∏ i ∈ w.support ∪ S', cut ρ S' i (w i) :=
        Finset.prod_subset Finset.subset_union_right fun i _ hiS => by simp [cut, hiS]

open scoped Classical in
theorem prod_dif_cut (ρ : ι → ℕ → ℝ) (S' : Finset ι) (v : ι →₀ ℕ) :
    v.prod (dif (cut ρ S')) = if v.support ⊆ S' then v.prod (dif ρ) else 0 := by
  split_ifs with h
  · unfold Finsupp.prod
    refine Finset.prod_congr rfl fun i hi => ?_
    have hiS : i ∈ S' := h hi
    cases v i with
    | zero => rfl
    | succ k =>
      show cut ρ S' i (k + 1) - cut ρ S' i k = ρ i (k + 1) - ρ i k
      simp [cut, hiS]
  · obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp h
    unfold Finsupp.prod
    refine Finset.prod_eq_zero hi ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    rw [hk]
    show cut ρ S' i (k + 1) - cut ρ S' i k = 0
    simp [cut, hiS]

open scoped Classical in
theorem euler_identity (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹)
    (S : Finset ι) {ρ : ι → ℕ → ℝ} (hρ0 : ∀ i, ρ i 0 = 1) (hρS : ∀ i ∈ S, ∀ j, ρ i j = 1)
    (hρb : ∀ i j, |ρ i (j + 1) - ρ i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i)
    (val : X → ι →₀ ℕ) (B : ℕ → Finset X) (a : X → ℝ) (sc : ℕ → ℝ) (c c0 C : ℝ) (E : ι → ℝ)
    (hc : c0 = 0 → c = 0)
    (H1 : ∀ v : ι →₀ ℕ, Disjoint v.support S →
      Tendsto (fun j => sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) atTop
        (𝓝 (c / nrm q v)))
    (H2 : ∀ᶠ j in atTop, ∀ v : ι →₀ ℕ,
      |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n| ≤ C / nrm q v)
    (H3 : ∀ S' : Finset ι, S ⊆ S' →
      Tendsto (fun j => sc j * ∑ n ∈ B j, a n * ∏ i ∈ S', ρ i (val n i)) atTop
        (𝓝 (c0 * ∏ i ∈ S', E i))) :
    c * ∑' v : ι →₀ ℕ, v.prod (dif ρ) / nrm q v = c0 * ∏' i, E i := by
  have key : ∀ S' : Finset ι, S ⊆ S' →
      c0 * ∏ i ∈ S', E i = c * ∑' v : ι →₀ ℕ,
        (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v := by
    intro S' hSS'
    have h0 : ∀ i, cut ρ S' i 0 = 1 := fun i => by simp [cut, hρ0]
    have hS : ∀ i ∈ S, ∀ j, cut ρ S' i j = 1 := fun i hi j => by
      simp [cut, hSS' hi, hρS i hi j]
    have hb : ∀ i j, |cut ρ S' i (j + 1) - cut ρ S' i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i := by
      intro i j
      by_cases hi : i ∈ S'
      · simpa [cut, hi] using hρb i j
      · simp only [cut, if_neg hi, sub_self, abs_zero]
        exact div_nonneg (by positivity) (by linarith [hq i])
    have hT := tendsto_weighted hq hsum S h0 hS hb val B a sc c C H1 H2
    have e1 : ∀ n, (val n).prod (cut ρ S') = ∏ i ∈ S', ρ i (val n i) :=
      fun n => prod_cut hρ0 S' (val n)
    have e2 : ∀ v : ι →₀ ℕ, v.prod (dif (cut ρ S')) =
        if v.support ⊆ S' then v.prod (dif ρ) else 0 :=
      fun v => prod_dif_cut ρ S' v
    simp only [e1, e2] at hT
    exact tendsto_nhds_unique (H3 S' hSS') hT
  set L := ∑' v : ι →₀ ℕ, v.prod (dif ρ) / nrm q v with hL
  have hG : Tendsto (fun S' : Finset ι => ∑' v : ι →₀ ℕ,
      (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v) atTop (𝓝 L) := by
    refine tendsto_tsum_of_dominated_convergence
      (f := fun S' v => (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v)
      (g := fun v => v.prod (dif ρ) / nrm q v)
      (bound := fun v => |v.prod (dif ρ)| / nrm q v)
      (summable_dif hq hsum hρb) ?_ ?_
    · intro v
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop v.support] with S' hS'
      try dsimp only
      rw [if_pos (show v.support ⊆ S' from hS')]
    · filter_upwards with S' v
      try dsimp only
      have hw := nrm_pos hq v
      split_ifs
      · rw [Real.norm_eq_abs, abs_div, abs_of_pos hw]
      · rw [zero_div, norm_zero]
        exact div_nonneg (abs_nonneg _) hw.le
  by_cases hc0 : c0 = 0
  · simp [hc0, hc hc0]
  · have hP : HasProd E (c * L / c0) := by
      have h1 : Tendsto (fun S' : Finset ι => c * (∑' v : ι →₀ ℕ,
          (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v) / c0) atTop
          (𝓝 (c * L / c0)) := (hG.const_mul c).div_const c0
      have h2 : (fun S' : Finset ι => c * (∑' v : ι →₀ ℕ,
          (if v.support ⊆ S' then v.prod (dif ρ) else 0) / nrm q v) / c0)
          =ᶠ[atTop] fun S' => ∏ i ∈ S', E i := by
        filter_upwards [eventually_ge_atTop S] with S' hS'
        rw [← key S' hS', mul_comm, mul_div_assoc, div_self hc0, mul_one]
      exact h1.congr' h2
    rw [hP.tprod_eq, mul_div_assoc', mul_comm c0, mul_div_assoc, div_self hc0, mul_one]

open scoped Classical in
theorem tendsto_weighted_tprod (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹)
    (S : Finset ι) {ρ : ι → ℕ → ℝ} (hρ0 : ∀ i, ρ i 0 = 1) (hρS : ∀ i ∈ S, ∀ j, ρ i j = 1)
    (hρb : ∀ i j, |ρ i (j + 1) - ρ i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i)
    (val : X → ι →₀ ℕ) (B : ℕ → Finset X) (a : X → ℝ) (sc : ℕ → ℝ) (c c0 C : ℝ) (E : ι → ℝ)
    (hc : c0 = 0 → c = 0)
    (H1 : ∀ v : ι →₀ ℕ, Disjoint v.support S →
      Tendsto (fun j => sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n) atTop
        (𝓝 (c / nrm q v)))
    (H2 : ∀ᶠ j in atTop, ∀ v : ι →₀ ℕ,
      |sc j * ∑ n ∈ (B j).filter (fun n => v ≤ val n), a n| ≤ C / nrm q v)
    (H3 : ∀ S' : Finset ι, S ⊆ S' →
      Tendsto (fun j => sc j * ∑ n ∈ B j, a n * ∏ i ∈ S', ρ i (val n i)) atTop
        (𝓝 (c0 * ∏ i ∈ S', E i))) :
    Tendsto (fun j => sc j * ∑ n ∈ B j, a n * (val n).prod ρ) atTop (𝓝 (c0 * ∏' i, E i)) := by
  have h := tendsto_weighted hq hsum S hρ0 hρS hρb val B a sc c C H1 H2
  rwa [euler_identity hq hsum S hρ0 hρS hρb val B a sc c c0 C E hc H1 H2 H3] at h

end Formalism.HermitianLattices.Ext.L3.A5
