import Mathlib

open Filter Topology

namespace PositivityTheory.Lord

def PO (f : ℂ → ℂ) (x : ℂ) (k : ℕ) : Prop :=
  ∃ H : ℂ → ℂ, AnalyticAt ℂ H x ∧ ∀ᶠ s in 𝓝[≠] x, H s = (s - x) ^ k * f s

def ZO (f : ℂ → ℂ) (x : ℂ) (m : ℕ) : Prop :=
  ∃ u : ℂ → ℂ, AnalyticAt ℂ u x ∧ u x ≠ 0 ∧ ∀ᶠ s in 𝓝[≠] x, f s = (s - x) ^ m * u s

variable {f g : ℂ → ℂ} {x : ℂ} {k l m n : ℕ}

theorem PO.mono (h : PO f x k) (hk : k ≤ l) : PO f x l := by
  obtain ⟨H, hH, hev⟩ := h
  refine ⟨fun s => (s - x) ^ (l - k) * H s,
    ((analyticAt_id.sub analyticAt_const).fun_pow _).fun_mul hH, ?_⟩
  filter_upwards [hev] with s hs
  rw [hs, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]

theorem PO.mul (hf : PO f x k) (hg : PO g x l) : PO (fun s => f s * g s) x (k + l) := by
  obtain ⟨H, hH, hevH⟩ := hf
  obtain ⟨G, hG, hevG⟩ := hg
  refine ⟨fun s => H s * G s, hH.fun_mul hG, ?_⟩
  filter_upwards [hevH, hevG] with s hs ht
  rw [hs, ht, pow_add]
  ring

theorem PO.of_analytic (hf : AnalyticAt ℂ f x) : PO f x 0 :=
  ⟨f, hf, Filter.Eventually.of_forall fun s => by rw [pow_zero, one_mul]⟩

theorem PO.congr (hf : PO f x k) (h : ∀ᶠ s in 𝓝[≠] x, f s = g s) : PO g x k := by
  obtain ⟨H, hH, hev⟩ := hf
  refine ⟨H, hH, ?_⟩
  filter_upwards [hev, h] with s h1 h2
  rw [h1, h2]

theorem PO.prod {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (K : ι → ℕ) (h : ∀ i ∈ t, PO (F i) x (K i)) :
    PO (fun s => ∏ i ∈ t, F i s) x (∑ i ∈ t, K i) := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact PositivityTheory.Lord.PO.of_analytic analyticAt_const
  · intro a t ha ih h
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ZO.inv (hf : ZO f x m) : PO (fun s => (f s)⁻¹) x m := by
  obtain ⟨u, hu, hux, hev⟩ := hf
  refine ⟨fun s => (u s)⁻¹, hu.fun_inv hux, ?_⟩
  have hne : ∀ᶠ s in 𝓝[≠] x, u s ≠ 0 :=
    nhdsWithin_le_nhds (hu.continuousAt.eventually_ne hux)
  filter_upwards [hev, hne, self_mem_nhdsWithin] with s hs hus hsx
  have hsx' : s - x ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsx)
  rw [hs, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hsx'), one_mul]

theorem ZO.mul (hf : ZO f x m) (hg : ZO g x n) : ZO (fun s => f s * g s) x (m + n) := by
  obtain ⟨u, hu, hux, hevu⟩ := hf
  obtain ⟨v, hv, hvx, hevv⟩ := hg
  refine ⟨fun s => u s * v s, hu.fun_mul hv, mul_ne_zero hux hvx, ?_⟩
  filter_upwards [hevu, hevv] with s hs ht
  rw [hs, ht, pow_add]
  ring

theorem ZO.pow (hf : ZO f x m) (n : ℕ) : ZO (fun s => f s ^ n) x (m * n) := by
  obtain ⟨u, hu, hux, hev⟩ := hf
  refine ⟨fun s => u s ^ n, hu.fun_pow n, pow_ne_zero n hux, ?_⟩
  filter_upwards [hev] with s hs
  rw [hs, mul_pow, pow_mul]

theorem ZO.of_analytic (hf : AnalyticAt ℂ f x) (h0 : f x ≠ 0) : ZO f x 0 :=
  ⟨f, hf, h0, Filter.Eventually.of_forall fun s => by rw [pow_zero, one_mul]⟩

theorem ZO.congr (hf : ZO f x m) (h : ∀ᶠ s in 𝓝[≠] x, f s = g s) : ZO g x m := by
  obtain ⟨u, hu, hux, hev⟩ := hf
  refine ⟨u, hu, hux, ?_⟩
  filter_upwards [hev, h] with s h1 h2
  rw [← h2, h1]

theorem ZO.prod {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (K : ι → ℕ) (h : ∀ i ∈ t, ZO (F i) x (K i)) :
    ZO (fun s => ∏ i ∈ t, F i s) x (∑ i ∈ t, K i) := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact PositivityTheory.Lord.ZO.of_analytic analyticAt_const one_ne_zero
  · intro a t ha ih h
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ZO.one_of_deriv (hf : AnalyticAt ℂ f x) (h0 : f x = 0) (hd : deriv f x ≠ 0) : ZO f x 1 := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨dslope f x, ⟨_, hp.has_fpower_series_dslope_fslope⟩, by rwa [dslope_same],
    Filter.Eventually.of_forall fun s => ?_⟩
  have h := sub_smul_dslope f x s
  rw [smul_eq_mul, h0, sub_zero] at h
  rw [pow_one, h]

theorem meromorphicAt_prod {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (h : ∀ i ∈ t, MeromorphicAt (F i) x) :
    MeromorphicAt (fun s => ∏ i ∈ t, F i s) x := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact MeromorphicAt.const 1 x
  · intro a t ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a t)).fun_mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end PositivityTheory.Lord
