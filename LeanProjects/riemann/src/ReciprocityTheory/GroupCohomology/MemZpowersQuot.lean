import Mathlib

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open Topology
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem comm_of_dense [T2Space G] {s : G} (hs : Dense (Subgroup.zpowers s : Set G)) (a b : G) :
    a * b = b * a := by
  have hcl : IsClosed {p : G × G | p.1 * p.2 = p.2 * p.1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst)
  have hd : Dense ((Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G)) := hs.prod hs
  have hsub : (Subgroup.zpowers s : Set G) ×ˢ (Subgroup.zpowers s : Set G) ⊆
      {p : G × G | p.1 * p.2 = p.2 * p.1} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact zpow_mul_comm s i j
  have h := hcl.closure_subset_iff.2 hsub
  rw [hd.closure_eq] at h
  exact h (Set.mem_univ (a, b))

theorem normal_of_comm (hc : ∀ a b : G, a * b = b * a) (W : Subgroup G) : W.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩

theorem finite_quot [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Finite (G ⧸ W) := by
  exact Subgroup.quotient_finite_of_isOpen W hW

theorem index_pos [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : 0 < W.index := by
  haveI := finite_quot hc hW
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite

variable {s : G}

theorem mem_zpowers_quot (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} [W.Normal]
    (hW : IsOpen (W : Set G)) (x : G ⧸ W) : x ∈ Subgroup.zpowers (QuotientGroup.mk' W s) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  obtain ⟨y, hyU, hy⟩ := hs.inter_open_nonempty _ hU ⟨g, by simp [W.one_mem]⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq.mpr hyU).symm

theorem zpow_mem_iff [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (z : ℤ) :
    s ^ z ∈ W ↔ (W.index : ℤ) ∣ z := by
  haveI := normal_of_comm hc W
  haveI := finite_quot hc hW
  have hord : orderOf (QuotientGroup.mk' W s) = W.index := by
    rw [orderOf_eq_card_of_forall_mem_zpowers (mem_zpowers_quot hs hW)]
    rfl
  rw [← QuotientGroup.eq_one_iff (N := W), ← hord, orderOf_dvd_iff_zpow_eq_one, ← map_zpow,
    QuotientGroup.mk'_apply]

theorem exists_pow [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G)) (g : G) :
    ∃ j : ℕ, g⁻¹ * s ^ j ∈ W := by
  haveI := normal_of_comm hc W
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_quot hs hW (g : G ⧸ W))
  rw [← map_zpow, QuotientGroup.mk'_apply] at hk
  have hgk : g⁻¹ * s ^ k ∈ W := QuotientGroup.eq.mp hk.symm
  have hn : (0 : ℤ) < W.index := by exact_mod_cast index_pos hc hW
  refine ⟨(k % (W.index : ℤ)).toNat, ?_⟩
  have hj : (((k % (W.index : ℤ)).toNat : ℕ) : ℤ) = k % (W.index : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')
  have hd : s ^ (k % (W.index : ℤ) - k) ∈ W := by
    rw [zpow_mem_iff hc hs hW]
    exact ⟨-(k / (W.index : ℤ)), by rw [Int.emod_def]; ring⟩
  have heq : g⁻¹ * s ^ (k % (W.index : ℤ)).toNat =
      (g⁻¹ * s ^ k) * s ^ (k % (W.index : ℤ) - k) := by
    rw [mul_assoc, ← zpow_add, ← zpow_natCast, hj]
    congr 2
    ring
  rw [heq]
  exact W.mul_mem hgk hd

section Desc

variable {X : Type*} (n : ℕ) (T : ℕ → X)

theorem per_mul (hper : ∀ j, T (j + n) = T j) (a t : ℕ) : T (a + n * t) = T a := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]

theorem per_of_dvd (hper : ∀ j, T (j + n) = T j) (a b : ℕ) (h : (n : ℤ) ∣ (b : ℤ) - a) :
    T a = T b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · have h1 : ((b : ℕ) : ℤ) = ((a + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : b = a + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]
  · rw [mul_neg] at hc
    have h1 : ((a : ℕ) : ℤ) = ((b + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : a = b + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]

end Desc

noncomputable def desc (W : Subgroup G) (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*}
    (T : ℕ → X) (g : G) : X :=
  T (Classical.choose (h g))

theorem desc_eq [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) {g : G} {j : ℕ} (hj : g⁻¹ * s ^ j ∈ W) :
    desc W h T g = T j := by
  have h0 := Classical.choose_spec (h g)
  show T (Classical.choose (h g)) = T j
  have hm : s ^ ((j : ℤ) - (Classical.choose (h g) : ℕ)) ∈ W := by
    have hw := W.mul_mem (W.inv_mem h0) hj
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    rw [zpow_sub, zpow_natCast, zpow_natCast, hc]
    exact hw
  exact per_of_dvd W.index T hper _ _ ((zpow_mem_iff hc hs hW _).mp hm)

theorem desc_continuous [CompactSpace G] (hc : ∀ a b : G, a * b = b * a)
    (hs : Dense (Subgroup.zpowers s : Set G)) {W : Subgroup G} (hW : IsOpen (W : Set G))
    (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*} [TopologicalSpace X] (T : ℕ → X)
    (hper : ∀ j, T (j + W.index) = T j) : Continuous (desc W h T) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hU : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (W : Set G)) :=
    hW.preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun y => g⁻¹ * y) ⁻¹' (W : Set G) := by simp [W.one_mem]
  refine (continuousAt_const : ContinuousAt (fun _ : G => desc W h T g) g).congr ?_
  filter_upwards [hU.mem_nhds hg] with y hy
  have h0 := Classical.choose_spec (h g)
  have hy' : y⁻¹ * s ^ Classical.choose (h g) ∈ W := by
    have hw := W.mul_mem (W.inv_mem hy) h0
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at hw
    exact hw
  rw [desc_eq hc hs hW h T hper hy']
  rfl

end ProcyclicCohomology

end ReciprocityTheory.Coh
