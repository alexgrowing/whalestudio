import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

namespace SubsetSumInvariance

open Equiv Equiv.Perm Finset

variable {α : Type} [Fintype α] [DecidableEq α]

def orbs (σ : Perm α) : Finset (Finset α) :=
  (σ.cycleFactorsFinset.image support) ∪ ((univ \ σ.support).image fun y => {y})

lemma fixed_of_not_mem {σ : Perm α} {y : α} (h : y ∉ σ.support) : σ y = y := Perm.notMem_support.1 h

lemma orbs_stable {σ : Perm α} {O : Finset α} (hO : O ∈ orbs σ) : ∀ x ∈ O, σ x ∈ O := by
  intro x hx
  rcases Finset.mem_union.1 hO with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    rw [← (Perm.mem_cycleFactorsFinset_iff.1 hc).2 x hx]
    exact Perm.apply_mem_support.2 hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_singleton] at hx ⊢
    subst hx
    exact fixed_of_not_mem (Finset.mem_sdiff.1 hy).2

lemma pow_stable {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) :
    ∀ m : ℕ, ∀ z ∈ A, (σ ^ m) z ∈ A := by
  intro m
  induction m with
  | zero => intro z hz; simpa using hz
  | succ m ih =>
    intro z hz
    rw [pow_succ', Perm.mul_apply]
    exact hA _ (ih z hz)

lemma orbs_sub {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) {O : Finset α}
    (hO : O ∈ orbs σ) {x : α} (hxO : x ∈ O) (hxA : x ∈ A) : O ⊆ A := by
  intro y hy
  rcases Finset.mem_union.1 hO with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    have hcx : c = σ.cycleOf x := Perm.cycle_is_cycleOf hxO hc
    rw [hcx, Perm.mem_support_cycleOf_iff] at hy
    obtain ⟨i, hi⟩ := hy.1.exists_nat_pow_eq
    rw [← hi]
    exact pow_stable hA i x hxA
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_singleton] at hy hxO
    rw [hy, ← hxO]
    exact hxA

lemma orbs_eq {σ : Perm α} {O O' : Finset α} (hO : O ∈ orbs σ) (hO' : O' ∈ orbs σ) {x : α}
    (h1 : x ∈ O) (h2 : x ∈ O') : O = O' := by
  have key : ∀ {O O' : Finset α}, O ∈ orbs σ → O' ∈ orbs σ → x ∈ O → x ∈ O' → O ⊆ O' := by
    intro O O' hO hO' h1 h2
    exact orbs_sub (fun y hy => orbs_stable hO' y hy) hO h1 h2
  exact Finset.Subset.antisymm (key hO hO' h1 h2) (key hO' hO h2 h1)

lemma orbs_pd (σ : Perm α) : (orbs σ : Set (Finset α)).PairwiseDisjoint id := by
  intro O hO O' hO' hne
  rw [Function.onFun, id, id, Finset.disjoint_left]
  intro x h1 h2
  exact hne (orbs_eq hO hO' h1 h2)

lemma orbs_parts (σ : Perm α) : (orbs σ).val.map Finset.card = σ.partition.parts := by
  have hdisj : Disjoint (σ.cycleFactorsFinset.image support) ((univ \ σ.support).image fun y => {y}) := by
    rw [Finset.disjoint_left]
    intro O h1 h2
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h2
    have h2le := (Perm.mem_cycleFactorsFinset_iff.1 hc).1.two_le_card_support
    rw [← hy, Finset.card_singleton] at h2le
    omega
  have hinj1 : Set.InjOn support (σ.cycleFactorsFinset : Set (Perm α)) := by
    intro c hc c' hc' h
    obtain ⟨a, ha⟩ := (Perm.mem_cycleFactorsFinset_iff.1 hc).1.nonempty_support
    rw [Perm.cycle_is_cycleOf ha hc, Perm.cycle_is_cycleOf (h ▸ ha) hc']
  have hinj2 : Set.InjOn (fun y : α => ({y} : Finset α)) ((univ \ σ.support : Finset α) : Set α) := by
    intro y _ z _ h
    exact Finset.singleton_injective h
  rw [orbs, ← Finset.disjUnion_eq_union _ _ hdisj, Finset.disjUnion_val, Multiset.map_add,
    Finset.image_val_of_injOn hinj1, Finset.image_val_of_injOn hinj2, Multiset.map_map, Multiset.map_map,
    Perm.parts_partition, Perm.cycleType_def]
  congr 1
  have : (Finset.card ∘ fun y : α => ({y} : Finset α)) = fun _ => 1 := by
    funext y
    simp
  rw [this, Multiset.map_const', Finset.card_val, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ]

end SubsetSumInvariance

namespace SubsetSumInvariance

lemma exists_le_map {β γ : Type*} (f : β → γ) (m : Multiset β) :
    ∀ s : Multiset γ, s ≤ m.map f → ∃ t ≤ m, t.map f = s := by
  classical
  induction m using Multiset.induction_on with
  | empty =>
    intro s hs
    refine ⟨0, le_rfl, ?_⟩
    simp only [Multiset.map_zero, nonpos_iff_eq_zero] at hs ⊢
    exact hs.symm
  | cons b m ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases hb : f b ∈ s
    · have hle : s.erase (f b) ≤ m.map f := by
        have := Multiset.erase_le_erase (f b) hs
        rwa [Multiset.erase_cons_head] at this
      obtain ⟨t, ht, htf⟩ := ih _ hle
      refine ⟨b ::ₘ t, Multiset.cons_le_cons b ht, ?_⟩
      rw [Multiset.map_cons, htf, Multiset.cons_erase hb]
    · obtain ⟨t, ht, htf⟩ := ih s ((Multiset.le_cons_of_notMem hb).1 hs)
      exact ⟨t, ht.trans (Multiset.le_cons_self _ _), htf⟩

end SubsetSumInvariance

open SubsetSumInvariance in
theorem exists_invariant_of_isSubSum {α : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (a : ℕ)
    (h : IsSubSum σ.partition.parts a) : ∃ A : Finset α, (∀ x ∈ A, σ x ∈ A) ∧ A.card = a := by
  obtain ⟨s, hs, hsum⟩ := h
  rw [← orbs_parts] at hs
  obtain ⟨t, ht, htf⟩ := exists_le_map Finset.card _ s hs
  let T : Finset (Finset α) := ⟨t, Multiset.nodup_of_le ht (orbs σ).nodup⟩
  have hT : T ⊆ orbs σ := fun O hO => Multiset.subset_of_le ht hO
  refine ⟨T.biUnion id, ?_, ?_⟩
  · intro x hx
    obtain ⟨O, hO, hxO⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨O, hO, orbs_stable (hT hO) x hxO⟩
  · rw [Finset.card_biUnion (fun O hO O' hO' hne => orbs_pd σ (hT hO) (hT hO') hne),
      Finset.sum_eq_multiset_sum]
    change (t.map fun O => (id O).card).sum = a
    simpa [htf] using hsum

theorem permutation_subset_sum_invariant : PermSubSumInv := by
  intro α _ _ σ a h
  obtain ⟨A, hA, hcard⟩ := exists_invariant_of_isSubSum σ a h
  exact ⟨A, hA, hcard⟩

end Formalism.GaloisIrreducibility
