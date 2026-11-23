import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.FsMetricFinIsSemipositive
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

namespace ProjPotDens

open ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockCLM (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (⟨k, i⟩ : Σ k, ι k)

omit [Fintype K] [∀ k, Fintype (ι k)] in
@[simp] theorem blockCLM_apply (k : K) (z : (Σ k, ι k) → ℂ) (i : ι k) :
    blockCLM k z i = z ⟨k, i⟩ := rfl

def fsMultiPot (z : (Σ k, ι k) → ℂ) : ℝ :=
  ∑ k, Real.log (∑ i, ‖z ⟨k, i⟩‖ ^ 2)

theorem levi_finset_sum {κ α : Type*} [Fintype κ] (s : Finset α) (F : α → (κ → ℂ) → ℝ)
    {z : κ → ℂ} (hF : ∀ a ∈ s, ContDiffAt ℝ 2 (F a) z) (v : κ → ℂ) :
    levi (fun y => ∑ a ∈ s, F a y) z v = ∑ a ∈ s, levi (F a) z v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi]
  | insert a s ha ih =>
    have hs : ContDiffAt ℝ 2 (fun y => ∑ b ∈ s, F b y) z :=
      ContDiffAt.sum fun b hb => hF b (Finset.mem_insert_of_mem hb)
    have h := levi_add_smul (f := F a) (g := fun y => ∑ b ∈ s, F b y) 1
      (hF a (Finset.mem_insert_self a s)) hs v
    simp only [one_mul] at h
    simp only [Finset.sum_insert ha]
    rw [h, ih fun b hb => hF b (Finset.mem_insert_of_mem hb)]

theorem levi_logBlock (k : K) {z : (Σ k, ι k) → ℂ} (hz : blockCLM k z ≠ 0)
    (v : (Σ k, ι k) → ℂ) :
    levi (fun y : (Σ k, ι k) → ℂ => Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2)) z v =
      2 * leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w)) (blockCLM k z) (blockCLM k v) := by
  have hne : fsLp (ι k) (blockCLM k z) ≠ 0 := fsLp_ne_zero hz
  have hg : ContDiffAt ℝ 2 (fun w : ι k → ℂ => Real.log ((fsMetric (ι k)).ρ w)) (blockCLM k z) :=
    ((contDiffAt_norm ℂ hne).comp _ (fsLp (ι k)).contDiff.contDiffAt).log
      (norm_ne_zero_iff.2 hne)
  have e : (fun y : (Σ k, ι k) → ℂ => Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2)) =
      (fun w => (fun _ => (0 : ℝ)) w + 2 * Real.log ((fsMetric (ι k)).ρ w)) ∘ blockCLM k := by
    funext y
    have hs : ∑ i, ‖y ⟨k, i⟩‖ ^ 2 = ‖fsLp (ι k) (blockCLM k y)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      rfl
    simp only [Function.comp_apply, zero_add]
    rw [hs, Real.log_pow]
    push_cast
    rfl
  rw [e, levi_comp v ((blockCLM k).analyticAt z)
      (contDiffAt_const.add (contDiffAt_const.mul hg)), (blockCLM k).fderiv,
    levi_add_smul 2 contDiffAt_const hg]
  have h0 : levi (fun _ : ι k → ℂ => (0 : ℝ)) (blockCLM k z) (blockCLM k v) = 0 := by
    unfold levi; simp
  rw [h0, zero_add]
  rfl

theorem levi_fsMultiPot (p : (k : K) → ι k) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) (v : (Σ k, ι k) → ℂ) :
    ContDiffAt ℝ 2 fsMultiPot z ∧ 0 ≤ levi fsMultiPot z v ∧
      ((∀ k, v ⟨k, p k⟩ = 0) → v ≠ 0 → 0 < levi fsMultiPot z v) := by
  have hb : ∀ k, blockCLM k z ≠ 0 := fun k h => hz k (by simpa using congrFun h (p k))
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k =>
    lt_of_lt_of_le (by have := norm_pos_iff.2 (hz k); positivity)
      (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ (p k)))
  have hC : ∀ k ∈ (Finset.univ : Finset K),
      ContDiffAt ℝ 2 (fun y : (Σ k, ι k) → ℂ => Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2)) z := fun k _ =>
    ((ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))).contDiffAt).log (hpos k).ne'
  have hsum : levi fsMultiPot z v = ∑ k, 2 * leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w))
      (blockCLM k z) (blockCLM k v) := by
    rw [show (fsMultiPot : ((Σ k, ι k) → ℂ) → ℝ) =
      fun y => ∑ k, Real.log (∑ i, ‖y ⟨k, i⟩‖ ^ 2) from rfl, levi_finset_sum _ _ hC]
    exact Finset.sum_congr rfl fun k _ => levi_logBlock k (hb k) v
  have hterm : ∀ k, 0 ≤ leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w))
      (blockCLM k z) (blockCLM k v) := fun k => fsMetric_isSemipositive.2 _ (hb k) _
  have hstrict : ∀ k, v ⟨k, p k⟩ = 0 → blockCLM k v ≠ 0 →
      0 < leviForm (fun w => Real.log ((fsMetric (ι k)).ρ w)) (blockCLM k z) (blockCLM k v) := by
    intro k hv hbv
    rw [leviForm_fsMetric (hb k)]
    have hb0 : fsLp (ι k) (blockCLM k z) ≠ 0 := fsLp_ne_zero (hb k)
    have ha0 : fsLp (ι k) (blockCLM k v) ≠ 0 := fsLp_ne_zero hbv
    have hlt : ‖inner ℂ (fsLp (ι k) (blockCLM k z)) (fsLp (ι k) (blockCLM k v))‖ <
        ‖fsLp (ι k) (blockCLM k z)‖ * ‖fsLp (ι k) (blockCLM k v)‖ := by
      refine lt_of_le_of_ne (norm_inner_le_norm _ _) fun heq => ?_
      obtain ⟨r, hr, hra⟩ := (norm_inner_eq_norm_iff hb0 ha0).1 heq
      have h1 := congrArg (fun u : EuclideanSpace ℂ (ι k) => u (p k)) hra
      simp only [fsLp_apply, PiLp.toLp_apply, PiLp.smul_apply, blockCLM_apply, smul_eq_mul] at h1
      rw [hv] at h1
      exact mul_ne_zero hr (hz k) h1.symm
    apply div_pos _ (by have := norm_pos_iff.2 hb0; positivity)
    nlinarith [mul_self_lt_mul_self (norm_nonneg _) hlt, norm_nonneg (fsLp (ι k) (blockCLM k z)),
      norm_nonneg (fsLp (ι k) (blockCLM k v))]
  refine ⟨ContDiffAt.sum hC, ?_, fun hv hv0 => ?_⟩
  · rw [hsum]
    exact Finset.sum_nonneg fun k _ => mul_nonneg zero_le_two (hterm k)
  · obtain ⟨⟨k, i⟩, hq⟩ := Function.ne_iff.1 hv0
    have hbv : blockCLM k v ≠ 0 := fun h => hq (by simpa using congrFun h i)
    rw [hsum]
    exact Finset.sum_pos' (fun k _ => mul_nonneg zero_le_two (hterm k))
      ⟨k, Finset.mem_univ _, mul_pos two_pos (hstrict k (hv k) hbv)⟩

end ProjPotDens

end GroundTheory.Heights₂.Heights.Targets
