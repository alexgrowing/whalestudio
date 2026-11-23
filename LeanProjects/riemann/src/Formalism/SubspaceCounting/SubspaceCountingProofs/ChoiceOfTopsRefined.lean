import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
import Formalism.SubspaceCounting.SubspaceCountingProofs.TopsChoicePartA

noncomputable section

open Finset

namespace Formalism.G0

namespace TopsChoiceProbabilityLemmas

open TopsConditionalProbabilityWindows

def Dep (S : Finset ℕ) (A : Finset ℕ → Prop) : Prop := ∀ t, A t ↔ A (t ∩ S)

theorem sum_powerset_union_disj {β : Type*} [AddCommMonoid β] (S R : Finset ℕ)
    (h : Disjoint S R) (F : Finset ℕ → β) :
    ∑ t ∈ (S ∪ R).powerset, F t = ∑ a ∈ S.powerset, ∑ b ∈ R.powerset, F (a ∪ b) := by
  induction R using Finset.induction_on generalizing F with
  | empty => simp
  | insert x R hx ih =>
    have hxS : x ∉ S := fun hs => disjoint_left.1 h hs (mem_insert_self x R)
    have h' : Disjoint S R := disjoint_of_subset_right (subset_insert x R) h
    rw [union_insert, sum_powerset_insert (by simp [hx, hxS])]
    rw [ih h', ih h' (fun t => F (insert x t))]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [sum_powerset_insert hx]
    congr 1
    apply sum_congr rfl
    intro b _
    rw [union_insert]

theorem w_union {S R a b : Finset ℕ} (δ : ℝ) (h : Disjoint S R) (ha : a ⊆ S) (hb : b ⊆ R) :
    δ ^ (a ∪ b).card * (1 - δ) ^ ((S ∪ R).card - (a ∪ b).card) =
      (δ ^ a.card * (1 - δ) ^ (S.card - a.card)) * (δ ^ b.card * (1 - δ) ^ (R.card - b.card)) := by
  have hab : Disjoint a b := disjoint_of_subset_left ha (disjoint_of_subset_right hb h)
  rw [card_union_of_disjoint hab, card_union_of_disjoint h]
  have h1 := card_le_card ha
  have h2 := card_le_card hb
  rw [show S.card + R.card - (a.card + b.card) = (S.card - a.card) + (R.card - b.card) by omega,
    pow_add, pow_add]
  ring

theorem prob_and_eq_mul_of_disjoint (S R : Finset ℕ) (δ : ℝ) (h : Disjoint S R) (A B : Finset ℕ → Prop) :
    P (S ∪ R) δ (fun t => A (t ∩ S) ∧ B (t ∩ R)) = P S δ A * P R δ B := by
  classical
  unfold P
  beta_reduce
  rw [sum_powerset_union_disj S R h, sum_mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  have ha' := mem_powerset.1 ha
  have hb' := mem_powerset.1 hb
  have e1 : (a ∪ b) ∩ S = a := by
    rw [union_inter_distrib_right, inter_eq_left.2 ha',
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hb' h.symm), union_empty]
  have e2 : (a ∪ b) ∩ R = b := by
    rw [union_inter_distrib_right, inter_eq_left.2 hb',
      disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left ha' h), empty_union]
  rw [e1, e2, w_union δ h ha' hb']
  by_cases hA : A a <;> by_cases hB : B b <;> simp [hA, hB]

theorem prob_true (S : Finset ℕ) (δ : ℝ) : P S δ (fun _ => True) = 1 := by
  unfold P
  simp only [if_true]
  rw [sum_pow_mul_eq_add_pow]
  simp

theorem P_nonneg {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (A : Finset ℕ → Prop) :
    0 ≤ P U δ A := by
  classical
  unfold P
  apply sum_nonneg
  intro t _
  split_ifs
  · exact w_nonneg h0 h1 _ _
  · exact le_rfl

theorem prob_marginal {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) (A : Finset ℕ → Prop) :
    P U δ (fun t => A (t ∩ S)) = P S δ A := by
  have h := prob_and_eq_mul_of_disjoint S (U \ S) δ disjoint_sdiff A (fun _ => True)
  rw [prob_true, mul_one] at h
  simp only [and_true] at h
  rw [← h, union_sdiff_of_subset hS]

theorem prob_eq_of_dependsOn {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) {A : Finset ℕ → Prop} (hA : Dep S A) :
    P U δ A = P S δ A := by
  rw [← prob_marginal δ hS A]
  congr 1
  funext t
  exact propext (hA t)

theorem prob_and_eq_mul_of_disjoint₂ {U S R : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) (hR : R ⊆ U) (h : Disjoint S R)
    {A B : Finset ℕ → Prop} (hA : Dep S A) (hB : Dep R B) :
    P U δ (fun t => A t ∧ B t) = P U δ A * P U δ B := by
  have hD : Dep (S ∪ R) (fun t => A t ∧ B t) := by
    intro t
    have e1 : t ∩ (S ∪ R) ∩ S = t ∩ S := by rw [inter_assoc, inter_eq_right.2 subset_union_left]
    have e2 : t ∩ (S ∪ R) ∩ R = t ∩ R := by rw [inter_assoc, inter_eq_right.2 subset_union_right]
    show A t ∧ B t ↔ A (t ∩ (S ∪ R)) ∧ B (t ∩ (S ∪ R))
    rw [hA (t ∩ (S ∪ R)), hB (t ∩ (S ∪ R)), e1, e2]
    exact and_congr (hA t) (hB t)
  rw [prob_eq_of_dependsOn δ (union_subset hS hR) hD, prob_eq_of_dependsOn δ hS hA, prob_eq_of_dependsOn δ hR hB, ← prob_and_eq_mul_of_disjoint S R δ h]
  congr 1
  funext t
  exact propext (and_congr (hA t) (hB t))

theorem prob_forall_eq_prod {ι : Type*} [DecidableEq ι] {U : Finset ℕ} (δ : ℝ) (F : Finset ι)
    (S : ι → Finset ℕ) (hS : ∀ i ∈ F, S i ⊆ U)
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (E : ι → Finset ℕ → Prop) (hE : ∀ i ∈ F, Dep (S i) (E i)) :
    P U δ (fun t => ∀ i ∈ F, E i t) = ∏ i ∈ F, P U δ (E i) := by
  induction F using Finset.induction_on with
  | empty => simpa using prob_true U δ
  | insert k F hk ih =>
    rw [prod_insert hk]
    have hS' : ∀ i ∈ F, S i ⊆ U := fun i hi => hS i (mem_insert_of_mem hi)
    have hd' : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j) :=
      fun i hi j hj hij => hd i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij
    have hE' : ∀ i ∈ F, Dep (S i) (E i) := fun i hi => hE i (mem_insert_of_mem hi)
    rw [← ih hS' hd' hE']
    have hD : Dep (F.biUnion S) (fun t => ∀ i ∈ F, E i t) := by
      intro t
      apply forall₂_congr
      intro i hi
      rw [hE' i hi t, hE' i hi (t ∩ F.biUnion S), inter_assoc,
        inter_eq_right.2 (subset_biUnion_of_mem S hi)]
    have hdisj : Disjoint (S k) (F.biUnion S) := by
      rw [disjoint_biUnion_right]
      intro i hi
      exact hd k (mem_insert_self k F) i (mem_insert_of_mem hi) (fun h => hk (h ▸ hi))
    rw [← prob_and_eq_mul_of_disjoint₂ δ (hS k (mem_insert_self k F)) (biUnion_subset.2 hS') hdisj
      (hE k (mem_insert_self k F)) hD]
    congr 1
    funext t
    exact propext (forall_mem_insert _ _ _)

theorem prob_not_eq_one_sub (U : Finset ℕ) (δ : ℝ) (A : Finset ℕ → Prop) :
    P U δ (fun t => ¬ A t) = 1 - P U δ A := by
  classical
  rw [← prob_true U δ, eq_sub_iff_add_eq]
  unfold P
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  by_cases h : A t <;> simp [h]

theorem prob_or_le_add {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (A B : Finset ℕ → Prop) :
    P U δ (fun t => A t ∨ B t) ≤ P U δ A + P U δ B := by
  classical
  unfold P
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro t _
  have := w_nonneg h0 h1 t.card (U.card - t.card)
  by_cases hA : A t <;> by_cases hB : B t <;> simp [hA, hB] <;> linarith

theorem sum_le_prob {S : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A : Finset ℕ → Prop}
    (Fam : Finset (Finset ℕ)) (hF : ∀ t ∈ Fam, t ⊆ S ∧ A t) :
    ∑ t ∈ Fam, δ ^ t.card * (1 - δ) ^ (S.card - t.card) ≤ P S δ A := by
  classical
  unfold P
  refine le_trans (le_of_eq (sum_congr rfl fun t ht => ?_))
    (sum_le_sum_of_subset_of_nonneg (fun t ht => mem_powerset.2 (hF t ht).1) ?_)
  · rw [if_pos (hF t ht).2]
  · intro t _ _
    split_ifs
    · exact w_nonneg h0 h1 _ _
    · exact le_rfl

theorem prob_le_card_eq_binUpper (S : Finset ℕ) (δ : ℝ) (N : ℕ) :
    P S δ (fun a => N ≤ a.card) = binUpper S.card δ N := by
  classical
  unfold P binUpper
  beta_reduce
  rw [show (∑ t ∈ S.powerset, _) = ∑ t ∈ S.powerset,
      (fun j => if N ≤ j then δ ^ j * (1 - δ) ^ (S.card - j) else 0) t.card from
    sum_congr rfl (fun t _ => by by_cases h : N ≤ t.card <;> simp [h])]
  rw [sum_powerset_apply_card (fun j => if N ≤ j then δ ^ j * (1 - δ) ^ (S.card - j) else 0)]
  simp only [nsmul_eq_mul, mul_ite, mul_zero]
  rw [← sum_filter]
  have hs : (range (S.card + 1)).filter (fun j => N ≤ j) = Icc N S.card := by
    ext j
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [hs]
  apply sum_congr rfl
  intro j _
  ring

theorem binUpper_mono_trials {m G : ℕ} (h : m ≤ G) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (N : ℕ) :
    binUpper m δ N ≤ binUpper G δ N := by
  have e1 := prob_le_card_eq_binUpper (range m) δ N
  have e2 := prob_le_card_eq_binUpper (range G) δ N
  rw [card_range] at e1 e2
  rw [← e1, ← e2, ← prob_marginal δ (range_subset_range.2 h)]
  apply P_mono h0 h1
  intro t _ hN
  exact hN.trans (card_le_card inter_subset_left)

theorem binUpper_mono_N (G : ℕ) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (N : ℕ) :
    binUpper G δ N ≤ binUpper G δ (N - 1) := by
  unfold binUpper
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (Nat.sub_le N 1) le_rfl)
  intro j _ _
  have : 0 ≤ 1 - δ := by linarith
  positivity

end TopsChoiceProbabilityLemmas

namespace TopsChoiceProbabilityLemmas

open TopsConditionalProbabilityWindows

def tile (r u s : ℕ) : Finset ℕ := Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))

def EC (r u s c : ℕ) (t : Finset ℕ) : Prop :=
  (Odd c → t ∩ cell r u s c = ∅) ∧ (Even c → ∃ x, t ∩ cell r u s c = {x} ∧ Even x)

theorem cell_eq {r u s c : ℕ} (hc : 1 ≤ c) :
    cell r u s c = Ico (s * ((6 * r + 1) * u) + (c - 1) * u)
      (s * ((6 * r + 1) * u) + (c - 1) * u + u) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  unfold cell
  simp only [Nat.add_sub_cancel]
  congr 1
  ring

theorem cell_card {r u s c : ℕ} (hc : 1 ≤ c) : (cell r u s c).card = u := by
  rw [cell_eq hc, Nat.card_Ico]
  omega

theorem cell_sub_tile {r u s c : ℕ} (hc : 1 ≤ c) (hc' : c ≤ 6 * r + 1) :
    cell r u s c ⊆ tile r u s := by
  rw [cell_eq hc]
  unfold tile
  have h1 : (c - 1) * u + u ≤ (6 * r + 1) * u := by
    have := Nat.mul_le_mul_right u (show c - 1 + 1 ≤ 6 * r + 1 by omega)
    rwa [add_mul, one_mul] at this
  have h2 : (s + 1) * ((6 * r + 1) * u) = s * ((6 * r + 1) * u) + (6 * r + 1) * u := by ring
  apply Ico_subset_Ico <;> omega

theorem cell_disjoint {r u s c c' : ℕ} (hc : 1 ≤ c) (hc' : 1 ≤ c') (h : c ≠ c') :
    Disjoint (cell r u s c) (cell r u s c') := by
  rw [cell_eq hc, cell_eq hc']
  rcases lt_or_gt_of_ne h with h | h
  · have : (c - 1) * u + u ≤ (c' - 1) * u := by
      have := Nat.mul_le_mul_right u (show c - 1 + 1 ≤ c' - 1 by omega)
      rwa [add_mul, one_mul] at this
    exact disjoint_left.2 fun x hx hx' => by rw [mem_Ico] at hx hx'; omega
  · have : (c' - 1) * u + u ≤ (c - 1) * u := by
      have := Nat.mul_le_mul_right u (show c' - 1 + 1 ≤ c - 1 by omega)
      rwa [add_mul, one_mul] at this
    exact disjoint_left.2 fun x hx hx' => by rw [mem_Ico] at hx hx'; omega

theorem tile_disjoint {r u s s' : ℕ} (h : s ≠ s') : Disjoint (tile r u s) (tile r u s') := by
  unfold tile
  rcases lt_or_gt_of_ne h with h | h
  · have := Nat.mul_le_mul_right ((6 * r + 1) * u) (show s + 1 ≤ s' by omega)
    exact disjoint_left.2 fun x hx hx' => by rw [mem_Ico] at hx hx'; omega
  · have := Nat.mul_le_mul_right ((6 * r + 1) * u) (show s' + 1 ≤ s by omega)
    exact disjoint_left.2 fun x hx hx' => by rw [mem_Ico] at hx hx'; omega

theorem even_card (a u : ℕ) : u / 2 ≤ ((Ico a (a + u)).filter Even).card := by
  have h := card_le_card_of_injOn (s := range (u / 2)) (t := (Ico a (a + u)).filter Even)
    (fun k => a + a % 2 + 2 * k) ?_ ?_
  · simpa using h
  · intro k hk
    simp only [coe_range, Set.mem_Iio] at hk
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ⟨a / 2 + a % 2 + k, by omega⟩⟩
  · intro k1 _ k2 _ h
    simp only at h
    omega

theorem marked_iff (t : Finset ℕ) (r u s : ℕ) :
    Marked t r u s ↔ ∀ c ∈ Icc 1 (6 * r + 1), EC r u s c t := by
  unfold Marked EC
  simp only [mem_Icc, and_imp]

theorem dep_EC (r u s c : ℕ) : Dep (cell r u s c) (EC r u s c) := by
  intro t
  unfold EC
  rw [inter_assoc, inter_self]

theorem marked_inter (t : Finset ℕ) (r u s : ℕ) :
    Marked t r u s ↔ Marked (t ∩ tile r u s) r u s := by
  unfold Marked
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  apply imp_congr_right
  intro hc'
  rw [inter_assoc, inter_eq_right.2 (cell_sub_tile hc hc')]

theorem tile_div {r u s x : ℕ} (h : x ∈ tile r u s) : x / ((6 * r + 1) * u) = s := by
  unfold tile at h
  rw [mem_Ico] at h
  exact Nat.div_eq_of_lt_le h.1 h.2

theorem tile_sub' {n r u s i₀ : ℕ} (hs : s < n / ((6 * r + 1) * u)) (hnot : i₀ ∉ tile r u s) :
    tile r u s ⊆ (range n).erase i₀ := by
  intro x hx
  have hx' := hx
  unfold tile at hx
  rw [mem_Ico] at hx
  have h2 := Nat.mul_le_mul_right ((6 * r + 1) * u) (show s + 1 ≤ n / ((6 * r + 1) * u) by omega)
  have h3 := Nat.div_mul_le_self n ((6 * r + 1) * u)
  rw [mem_erase, mem_range]
  refine ⟨fun hxi => hnot (hxi ▸ hx'), by omega⟩

theorem marked_insert (t : Finset ℕ) {r u s i₀ : ℕ} (hnot : i₀ ∉ tile r u s) :
    Marked (insert i₀ t) r u s ↔ Marked t r u s := by
  unfold Marked
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  apply imp_congr_right
  intro hc'
  rw [insert_inter_of_notMem (fun h => hnot (cell_sub_tile hc hc' h))]

theorem prod_g (X Y : ℝ) (m : ℕ) :
    ∏ c ∈ Icc 1 (2 * m + 1), (if Odd c then X else Y) = X ^ (m + 1) * Y ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by ring, prod_Icc_succ_top (by omega),
      show 2 * m + 2 = (2 * m + 1) + 1 by ring, prod_Icc_succ_top (by omega), ih]
    have h1 : ¬ Odd (2 * m + 1 + 1) := by
      rw [Nat.not_odd_iff_even]
      exact ⟨m + 1, by ring⟩
    have h2 : Odd (2 * m + 1 + 1 + 1) := ⟨m + 1, by ring⟩
    rw [if_neg h1, if_pos h2]
    ring

theorem EC_ge {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {r u s c : ℕ} (hc : 1 ≤ c)
    (hU : cell r u s c ⊆ U) :
    (if Odd c then (1 - δ) ^ u else ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) ≤
      P U δ (EC r u s c) := by
  classical
  rw [prob_eq_of_dependsOn δ hU (dep_EC r u s c)]
  split_ifs with hodd
  · have := sum_le_prob (S := cell r u s c) (A := EC r u s c) h0 h1 {∅} (by
      intro t ht
      rw [mem_singleton] at ht
      subst ht
      exact ⟨empty_subset _, fun _ => empty_inter _,
        fun he => absurd hodd (Nat.not_odd_iff_even.2 he)⟩)
    simpa [cell_card hc] using this
  · have hev : Even c := Nat.not_odd_iff_even.1 hodd
    have := sum_le_prob (S := cell r u s c) (A := EC r u s c) h0 h1
      (((cell r u s c).filter Even).image (fun x => {x})) (by
      intro t ht
      rw [mem_image] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      rw [mem_filter] at hx
      exact ⟨singleton_subset_iff.2 hx.1, fun ho => absurd ho hodd,
        fun _ => ⟨x, inter_eq_left.2 (singleton_subset_iff.2 hx.1), hx.2⟩⟩)
    rw [sum_image (fun x _ y _ h => singleton_injective h)] at this
    simp only [card_singleton, pow_one, cell_card hc, sum_const, nsmul_eq_mul] at this
    refine le_trans ?_ this
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg h0 (pow_nonneg (by linarith) _))
    have := even_card (s * ((6 * r + 1) * u) + (c - 1) * u) u
    rw [← cell_eq hc] at this
    exact_mod_cast this

theorem marked_ge {U : Finset ℕ} {δ : ℝ} {r u s : ℕ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hT : tile r u s ⊆ U) :
    markedBound δ r u ≤ P U δ (fun t => Marked t r u s) := by
  classical
  have hcU : ∀ c ∈ Icc 1 (6 * r + 1), cell r u s c ⊆ U :=
    fun c hc => (cell_sub_tile (mem_Icc.1 hc).1 (mem_Icc.1 hc).2).trans hT
  have e : P U δ (fun t => Marked t r u s) =
      ∏ c ∈ Icc 1 (6 * r + 1), P U δ (EC r u s c) := by
    rw [← prob_forall_eq_prod δ (Icc 1 (6 * r + 1)) (cell r u s) hcU
      (fun c hc c' hc' hne => cell_disjoint (mem_Icc.1 hc).1 (mem_Icc.1 hc').1 hne)
      (EC r u s) (fun c _ => dep_EC r u s c)]
    congr 1
    funext t
    exact propext (marked_iff t r u s)
  rw [e]
  have hg := prod_g ((1 - δ) ^ u) (((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) (3 * r)
  rw [show 2 * (3 * r) + 1 = 6 * r + 1 by ring] at hg
  unfold markedBound
  rw [← hg]
  apply prod_le_prod
  · intro c _
    have : 0 ≤ 1 - δ := by linarith
    split_ifs
    · positivity
    · positivity
  · intro c hc
    exact EC_ge h0 h1 (mem_Icc.1 hc).1 (hcU c hc)

end TopsChoiceProbabilityLemmas

namespace TopsChoiceProbabilityLemmas

open TopsConditionalProbabilityWindows

theorem condProbAt_eq (n : ℕ) (δ : ℝ) (i₀ : ℕ) (hi : i₀ < n) (A : Finset ℕ → Prop) :
    condProbAt n δ i₀ A = P ((range n).erase i₀) δ (fun t => A (insert i₀ t)) := by
  classical
  have h0 : i₀ ∈ range n := mem_range.2 hi
  have hU : range n = insert i₀ ((range n).erase i₀) := (insert_erase h0).symm
  have hc : ((range n).erase i₀).card = n - 1 := by rw [card_erase_of_mem h0, card_range]
  unfold condProbAt P
  conv_lhs => rw [hU]
  rw [sum_powerset_insert (notMem_erase i₀ _)]
  rw [sum_eq_zero (fun t ht => ?_), zero_add]
  · apply sum_congr rfl
    intro t ht
    have h0t : i₀ ∉ t := fun h => notMem_erase i₀ (range n) (mem_powerset.1 ht h)
    have hnt : n - (t.card + 1) = n - 1 - t.card := by omega
    rw [card_insert_of_notMem h0t, hc, hnt]
    by_cases hA : A (insert i₀ t)
    · rw [if_pos ⟨mem_insert_self i₀ t, hA⟩, if_pos hA]
      simp
    · rw [if_neg (fun h => hA h.2), if_neg hA]
  · have h0t : i₀ ∉ t := fun h => notMem_erase i₀ (range n) (mem_powerset.1 ht h)
    rw [if_neg (fun h => h0t h.1)]

theorem card_insert_inter (a : ℕ) (t W : Finset ℕ) :
    (insert a t ∩ W).card ≤ (t ∩ W.erase a).card + 1 := by
  calc (insert a t ∩ W).card ≤ (insert a (t ∩ W.erase a)).card := card_le_card ?_
    _ ≤ _ := card_insert_le _ _
  intro x hx
  rw [mem_inter, mem_insert] at hx
  rw [mem_insert, mem_inter, mem_erase]
  by_cases h : x = a
  · left; exact h
  · right
    rcases hx with ⟨hx | hx, hw⟩
    · exact absurd hx h
    · exact ⟨hx, h, hw⟩

theorem partA (n : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (L₂ K i₀ : ℕ) (hn : 1 ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K) ≤
      n * (L₂.choose K : ℝ) * δ ^ K := by
  classical
  let F : ℕ → Finset (Finset ℕ) := fun i => powersetCard K ((window n i L₂).erase i₀)
  calc _ ≤ P ((range n).erase i₀) δ (fun t => ∃ i ∈ range n, ∃ S ∈ F i, S ⊆ t) := by
        apply P_mono h0 h1
        intro t _ h
        unfold CondA at h
        push Not at h
        obtain ⟨i, hi, hK⟩ := h
        have hc := card_insert_inter i₀ t (window n i L₂)
        obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq
          (show K ≤ (t ∩ (window n i L₂).erase i₀).card by omega)
        exact ⟨i, mem_range.2 hi, S, mem_powersetCard.2 ⟨hS.trans inter_subset_right, hSc⟩,
          hS.trans inter_subset_left⟩
    _ ≤ ∑ i ∈ range n, P ((range n).erase i₀) δ (fun t => ∃ S ∈ F i, S ⊆ t) :=
        prob_exists_le_sum h0 h1 (range n) (fun i t => ∃ S ∈ F i, S ⊆ t)
    _ ≤ ∑ i ∈ range n, ∑ S ∈ F i, P ((range n).erase i₀) δ (fun t => S ⊆ t) :=
        sum_le_sum fun i _ => prob_exists_le_sum h0 h1 (F i) (fun S t => S ⊆ t)
    _ = ∑ i ∈ range n, ∑ S ∈ F i, δ ^ S.card := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro S hS
        apply prob_subset_eq_pow_card
        exact (mem_powersetCard.1 hS).1.trans (erase_subset_erase i₀ (window_subset n i L₂ hn))
    _ = ∑ i ∈ range n, (((window n i L₂).erase i₀).card.choose K : ℝ) * δ ^ K := by
        apply sum_congr rfl
        intro i _
        rw [sum_congr rfl (fun S hS => by rw [(mem_powersetCard.1 hS).2]), sum_const,
          card_powersetCard, nsmul_eq_mul]
    _ ≤ ∑ i ∈ range n, (L₂.choose K : ℝ) * δ ^ K := by
        apply sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg h0 _)
        exact_mod_cast Nat.choose_le_choose K (card_erase_le.trans (window_card n i L₂))
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem partC (n : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (G' N₁ i₀ : ℕ) (hn : 1 ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondIntervals n (insert i₀ t) G' N₁) ≤
      n * binUpper G' δ (N₁ - 1) := by
  classical
  calc _ ≤ P ((range n).erase i₀) δ
        (fun t => ∃ i ∈ range n, N₁ ≤ (t ∩ (window n i G').erase i₀).card) := by
        apply P_mono h0 h1
        intro t _ h
        unfold CondIntervals at h
        push Not at h
        obtain ⟨i, hi, hN⟩ := h
        have hc := card_insert_inter i₀ t (window n i G')
        exact ⟨i, mem_range.2 hi, by omega⟩
    _ ≤ ∑ i ∈ range n, P ((range n).erase i₀) δ
        (fun t => N₁ ≤ (t ∩ (window n i G').erase i₀).card) :=
        prob_exists_le_sum h0 h1 (range n) (fun i t => N₁ ≤ (t ∩ (window n i G').erase i₀).card)
    _ = ∑ i ∈ range n, binUpper ((window n i G').erase i₀).card δ N₁ := by
        apply sum_congr rfl
        intro i _
        exact (prob_marginal δ (erase_subset_erase i₀ (window_subset n i G' hn))
          (fun a => N₁ ≤ a.card)).trans (prob_le_card_eq_binUpper _ δ N₁)
    _ ≤ ∑ i ∈ range n, binUpper G' δ (N₁ - 1) := by
        apply sum_le_sum
        intro i _
        exact (binUpper_mono_trials (card_erase_le.trans (window_card n i G')) h0 h1 N₁).trans
          (binUpper_mono_N G' h0 h1 N₁)
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

theorem tiles_bound {n : ℕ} {δ : ℝ} {r u M₀ i₀ : ℕ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) (s₀ : ℕ) (hs₀ : s₀ < n / ((6 * r + 1) * u)) :
    P ((range n).erase i₀) δ (fun t => ∀ j ≤ M₀,
      ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))) ≤
      (1 - markedBound δ r u) ^ M₀ := by
  classical
  have hℓpos : 0 < (6 * r + 1) * u := Nat.mul_pos (by omega) (by omega)
  have hM : M₀ + 1 ≤ n / ((6 * r + 1) * u) := (Nat.le_div_iff_mul_le hℓpos).2 hn
  set tt := n / ((6 * r + 1) * u) with htt
  set J := (range (M₀ + 1)).image (fun j => (s₀ + j) % tt) with hJdef
  have hJ : J.card = M₀ + 1 := by
    rw [card_image_of_injOn, card_range]
    intro j hj j' hj' h
    simp only [coe_range, Set.mem_Iio] at hj hj'
    have := Nat.ModEq.add_left_cancel' s₀ h
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hF : M₀ ≤ (J.erase (i₀ / ((6 * r + 1) * u))).card := by
    have := pred_card_le_card_erase (s := J) (a := i₀ / ((6 * r + 1) * u))
    omega
  obtain ⟨F, hFs, hFc⟩ := exists_subset_card_eq hF
  have hFmem : ∀ s ∈ F, s ≠ i₀ / ((6 * r + 1) * u) ∧ s < tt ∧ ∃ j ≤ M₀, (s₀ + j) % tt = s := by
    intro s hs
    have := hFs hs
    rw [mem_erase, mem_image] at this
    obtain ⟨hs0, j, hj, hjs⟩ := this
    exact ⟨hs0, hjs ▸ Nat.mod_lt _ (by omega), j, by have := mem_range.1 hj; omega, hjs⟩
  have hnot : ∀ s ∈ F, i₀ ∉ tile r u s := fun s hs hmem => (hFmem s hs).1 (tile_div hmem).symm
  have hsub : ∀ s ∈ F, tile r u s ⊆ (range n).erase i₀ :=
    fun s hs => tile_sub' (hFmem s hs).2.1 (hnot s hs)
  calc _ ≤ P ((range n).erase i₀) δ (fun t => ∀ s ∈ F, ¬ Marked t r u s) := by
        apply P_mono h0 h1
        intro t _ h s hs
        obtain ⟨_, _, j, hj, hjs⟩ := hFmem s hs
        rw [← marked_insert t (hnot s hs), ← hjs]
        exact h j hj
    _ = ∏ s ∈ F, P ((range n).erase i₀) δ (fun t => ¬ Marked t r u s) :=
        prob_forall_eq_prod δ F (tile r u) hsub (fun s _ s' _ hne => tile_disjoint hne)
          (fun s t => ¬ Marked t r u s) (fun s _ t => not_congr (marked_inter t r u s))
    _ ≤ ∏ s ∈ F, (1 - markedBound δ r u) := by
        apply prod_le_prod
        · intro s _
          exact P_nonneg h0 h1 _
        · intro s hs
          rw [prob_not_eq_one_sub]
          linarith [marked_ge (r := r) (u := u) (s := s) h0 h1 (hsub s hs)]
    _ = _ := by rw [prod_const, hFc]

theorem partB {n : ℕ} {δ : ℝ} {r u M₀ i₀ : ℕ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) :
    P ((range n).erase i₀) δ (fun t => ¬ CondTiles n (insert i₀ t) r u M₀) ≤
      n * (1 - markedBound δ r u) ^ M₀ := by
  classical
  have hℓpos : 0 < (6 * r + 1) * u := Nat.mul_pos (by omega) (by omega)
  have hM : M₀ + 1 ≤ n / ((6 * r + 1) * u) := (Nat.le_div_iff_mul_le hℓpos).2 hn
  have hX : ∀ s₀ ∈ range (n / ((6 * r + 1) * u)), P ((range n).erase i₀) δ (fun t => ∀ j ≤ M₀,
      ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))) ≤
      (1 - markedBound δ r u) ^ M₀ :=
    fun s₀ hs => tiles_bound h0 h1 hu hn s₀ (mem_range.1 hs)
  have hX0 : 0 ≤ (1 - markedBound δ r u) ^ M₀ :=
    le_trans (P_nonneg h0 h1 _) (hX 0 (mem_range.2 (by omega)))
  calc _ ≤ ∑ s₀ ∈ range (n / ((6 * r + 1) * u)), P ((range n).erase i₀) δ (fun t => ∀ j ≤ M₀,
        ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))) := by
        refine le_trans (P_mono h0 h1 ?_) (prob_exists_le_sum h0 h1 (range (n / ((6 * r + 1) * u)))
          (fun s₀ t => ∀ j ≤ M₀, ¬ Marked (insert i₀ t) r u ((s₀ + j) % (n / ((6 * r + 1) * u)))))
        intro t _ h
        unfold CondTiles at h
        push Not at h
        obtain ⟨s₀, hs, h⟩ := h
        exact ⟨s₀, mem_range.2 hs, h⟩
    _ ≤ ∑ s₀ ∈ range (n / ((6 * r + 1) * u)), (1 - markedBound δ r u) ^ M₀ := sum_le_sum hX
    _ = ((n / ((6 * r + 1) * u) : ℕ) : ℝ) * (1 - markedBound δ r u) ^ M₀ := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ n * (1 - markedBound δ r u) ^ M₀ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.div_le_self n _) hX0

end TopsChoiceProbabilityLemmas

open TopsChoiceProbabilityLemmas TopsConditionalProbabilityWindows in
theorem choice_of_tops_refined_holds : TileConditionFailureProbBound := by
  classical
  intro n δ L₂ K r u M₀ G' N₁ i₀ h0 h1 hr hu hn hi
  have hn1 : 1 ≤ n := by omega
  rw [condProbAt_eq n δ i₀ hi]
  calc P ((range n).erase i₀) δ (fun t => ¬ GoodOrbitIntervalTileCondition n (insert i₀ t) L₂ K r u M₀ G' N₁)
      ≤ P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K ∨
          (¬ CondTiles n (insert i₀ t) r u M₀ ∨ ¬ CondIntervals n (insert i₀ t) G' N₁)) := by
        apply P_mono h0 h1
        intro t _ h
        unfold GoodOrbitIntervalTileCondition at h
        tauto
    _ ≤ P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K) +
          P ((range n).erase i₀) δ (fun t => ¬ CondTiles n (insert i₀ t) r u M₀ ∨
            ¬ CondIntervals n (insert i₀ t) G' N₁) :=
        prob_or_le_add h0 h1 (fun t => ¬ CondA n (insert i₀ t) L₂ K)
          (fun t => ¬ CondTiles n (insert i₀ t) r u M₀ ∨ ¬ CondIntervals n (insert i₀ t) G' N₁)
    _ ≤ P ((range n).erase i₀) δ (fun t => ¬ CondA n (insert i₀ t) L₂ K) +
          (P ((range n).erase i₀) δ (fun t => ¬ CondTiles n (insert i₀ t) r u M₀) +
            P ((range n).erase i₀) δ (fun t => ¬ CondIntervals n (insert i₀ t) G' N₁)) :=
        add_le_add le_rfl (prob_or_le_add h0 h1 (fun t => ¬ CondTiles n (insert i₀ t) r u M₀)
          (fun t => ¬ CondIntervals n (insert i₀ t) G' N₁))
    _ ≤ n * (L₂.choose K : ℝ) * δ ^ K + (n * (1 - markedBound δ r u) ^ M₀ +
          n * binUpper G' δ (N₁ - 1)) :=
        add_le_add (partA n δ h0 h1 L₂ K i₀ hn1)
          (add_le_add (partB h0 h1 hu hn) (partC n δ h0 h1 G' N₁ i₀ hn1))
    _ = _ := by ring

end Formalism.G0
