import Mathlib

open Filter Topology Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {ι : Type*}

def ebox (s : Finset ι) (J : ι → ℕ) : Finset (ι →₀ ℕ) := s.finsupp fun i => range (J i + 1)

theorem mem_ebox {s : Finset ι} {J : ι → ℕ} {v : ι →₀ ℕ} :
    v ∈ ebox s J ↔ v.support ⊆ s ∧ ∀ i ∈ s, v i ≤ J i := by
  classical
  simp [ebox, Finset.mem_finsupp_iff, Nat.lt_succ_iff]

theorem sum_ebox (f : ι → ℕ → ℝ) (hf : ∀ i, f i 0 = 1) (s : Finset ι) (J : ι → ℕ) :
    ∑ v ∈ ebox s J, v.prod f = ∏ i ∈ s, ∑ j ∈ range (J i + 1), f i j := by
  classical
  rw [Finset.prod_sum, ebox, Finset.finsupp, Finset.sum_map]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Finsupp.prod_of_support_subset _ (Finsupp.support_indicator_subset s g) _ (fun i _ => hf i),
    ← Finset.prod_attach s]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.indicator_apply, dif_pos i.2]

theorem mem_ebox_support {v w : ι →₀ ℕ} : v ∈ ebox w.support w ↔ v ≤ w := by
  rw [mem_ebox, Finsupp.le_def]
  constructor
  · rintro ⟨hs, hle⟩ i
    by_cases hi : i ∈ w.support
    · exact hle i hi
    · have h0 : v i = 0 := by
        by_contra h
        exact hi (hs (Finsupp.mem_support_iff.mpr h))
      rw [h0]
      exact Nat.zero_le _
  · intro h
    refine ⟨fun i hi => ?_, fun i _ => h i⟩
    rw [Finsupp.mem_support_iff] at hi ⊢
    have := h i
    omega

def dif (R : ι → ℕ → ℝ) (i : ι) : ℕ → ℝ
  | 0 => 1
  | j + 1 => R i (j + 1) - R i j

theorem sum_dif (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), dif R i j = R i J := by
  induction J with
  | zero => simp [dif, hR]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    simp [dif]

theorem prod_eq_sum_dif (R : ι → ℕ → ℝ) (hR : ∀ i, R i 0 = 1) (w : ι →₀ ℕ) :
    w.prod R = ∑ v ∈ ebox w.support w, v.prod (dif R) := by
  rw [sum_ebox (dif R) (fun i => rfl) w.support w, Finsupp.prod]
  exact Finset.prod_congr rfl fun i _ => (sum_dif R hR i (w i)).symm

theorem summable_prod {u : ι → ℕ → ℝ} (hu0 : ∀ i, u i 0 = 1) (hu : ∀ i j, 0 ≤ u i j) {t : ι → ℝ}
    (ht : Summable t) (hut : ∀ i J, ∑ j ∈ range (J + 1), u i j ≤ 1 + t i) :
    Summable fun v : ι →₀ ℕ => v.prod u := by
  classical
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    have h := hut i 0
    simp [hu0] at h
    linarith
  apply summable_of_sum_le (c := Real.exp (∑' i, t i)) (fun v => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
  intro F
  have hsub : F ⊆ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i) := by
    intro v hv
    rw [mem_ebox]
    exact ⟨fun i hi => Finset.mem_biUnion.mpr ⟨v, hv, hi⟩,
      fun i _ => Finset.le_sup (f := fun v : ι →₀ ℕ => v i) hv⟩
  calc ∑ v ∈ F, v.prod u
      ≤ ∑ v ∈ ebox (F.biUnion fun v => v.support) (fun i => F.sup fun v => v i), v.prod u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun v _ _ => by unfold Finsupp.prod; exact Finset.prod_nonneg fun i _ => hu i _)
    _ = ∏ i ∈ F.biUnion (fun v => v.support), ∑ j ∈ range ((F.sup fun v => v i) + 1), u i j :=
        sum_ebox u hu0 _ _
    _ ≤ ∏ i ∈ F.biUnion (fun v => v.support), Real.exp (t i) := by
        apply Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => hu i j)
        intro i _
        calc _ ≤ 1 + t i := hut i _
          _ ≤ Real.exp (t i) := by linarith [Real.add_one_le_exp (t i)]
    _ = Real.exp (∑ i ∈ F.biUnion (fun v => v.support), t i) := (Real.exp_sum _ t).symm
    _ ≤ Real.exp (∑' i, t i) := Real.exp_le_exp.mpr (ht.sum_le_tsum _ (fun i _ => ht0 i))

theorem summable_sq_geom : Summable fun j : ℕ => 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
  have h0 := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  refine (((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left 8).congr fun j => ?_
  first
    | ring
    | (simp only [Pi.add_apply]; ring)
    | (simp; ring)

def cGeom : ℝ := ∑' j : ℕ, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j

variable {q : ι → ℝ}

def nrm (q : ι → ℝ) (v : ι →₀ ℕ) : ℝ := v.prod fun i e => q i ^ e

theorem nrm_pos (hq : ∀ i, 2 ≤ q i) (v : ι →₀ ℕ) : 0 < nrm q v := by
  unfold nrm Finsupp.prod
  exact Finset.prod_pos fun i _ => pow_pos (by linarith [hq i]) _

theorem abs_div_nrm (f : ι → ℕ → ℝ) (v : ι →₀ ℕ) :
    |v.prod f| / nrm q v = v.prod fun i e => |f i e| / q i ^ e := by
  unfold nrm Finsupp.prod
  rw [Finset.abs_prod, ← Finset.prod_div_distrib]

theorem sum_dif_le (hq : ∀ i, 2 ≤ q i) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) (i : ι) (J : ℕ) :
    ∑ j ∈ range (J + 1), |dif R i j| / q i ^ j ≤ 1 + cGeom * (q i ^ 2)⁻¹ := by
  have hq0 : 0 < q i := by linarith [hq i]
  rw [Finset.sum_range_succ']
  simp only [dif, pow_zero, div_one, abs_one]
  rw [add_comm]
  refine add_le_add le_rfl ?_
  have hterm : ∀ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1) ≤
      (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) := by
    intro j _
    have hqj : 0 < q i ^ (j + 1) := pow_pos hq0 _
    have hqne : q i ≠ 0 := hq0.ne'
    rw [div_le_iff₀ hqj]
    have hx : 1 ≤ (q i / 2) ^ j := one_le_pow₀ (by linarith [hq i])
    have hc : 0 ≤ 8 * ((j : ℝ) + 2) ^ 2 := by positivity
    have e : (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1) =
        8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
      have h2 : (q i ^ 2)⁻¹ * q i ^ (j + 1) = q i ^ j / q i := by
        rw [pow_succ (q i) j, sq]
        first
          | (field_simp; ring)
          | field_simp
      calc (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) * q i ^ (j + 1)
          = 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j * ((q i ^ 2)⁻¹ * q i ^ (j + 1)) := by ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * ((1 / 2 : ℝ) ^ j * q i ^ j) / q i := by rw [h2]; ring
        _ = 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by rw [← mul_pow]; ring_nf
    rw [e]
    calc |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i := hRb i j
      _ ≤ 8 * ((j : ℝ) + 2) ^ 2 * (q i / 2) ^ j / q i := by
        first
          | exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hc hx) hq0.le
          | exact (div_le_div_iff_of_pos_right hq0).mpr (le_mul_of_one_le_right hc hx)
          | exact (div_le_div_right hq0).mpr (le_mul_of_one_le_right hc hx)
  calc ∑ j ∈ range J, |R i (j + 1) - R i j| / q i ^ (j + 1)
      ≤ ∑ j ∈ range J, (q i ^ 2)⁻¹ * (8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j) :=
        Finset.sum_le_sum hterm
    _ = (q i ^ 2)⁻¹ * ∑ j ∈ range J, 8 * ((j : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (q i ^ 2)⁻¹ * cGeom := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact summable_sq_geom.sum_le_tsum _ (fun j _ => by positivity)
    _ = cGeom * (q i ^ 2)⁻¹ := mul_comm _ _

theorem summable_dif (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) :
    Summable fun v : ι →₀ ℕ => |v.prod (dif R)| / nrm q v := by
  have h := summable_prod (u := fun i e => |dif R i e| / q i ^ e) (fun i => by simp [dif])
    (fun i j => div_nonneg (abs_nonneg _) (pow_nonneg (by linarith [hq i]) _))
    (hsum.mul_left cGeom) (fun i J => sum_dif_le hq hRb i J)
  exact h.congr fun v => (abs_div_nrm (dif R) v).symm

end Formalism.HermitianLattices.Ext.L3.A5
