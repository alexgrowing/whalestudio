import Mathlib
import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition

noncomputable section

open scoped BigOperators
open Finset Formalism.G0

namespace GlobalTheory.RandomTops

def ex (δ : ℝ) (S : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ S.powerset, δ ^ T.card * (1 - δ) ^ (S.card - T.card) * f T

open Classical in

def ind (p : Prop) : ℝ := if p then 1 else 0

theorem ind_pos {p : Prop} (h : p) : ind p = 1 := by
  unfold ind
  rw [if_pos h]
theorem ind_neg {p : Prop} (h : ¬ p) : ind p = 0 := by
  unfold ind
  rw [if_neg h]
theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by
  unfold ind
  split_ifs <;> norm_num
theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num
theorem ind_le {p : Prop} {x : ℝ} (h0 : 0 ≤ x) (h1 : p → 1 ≤ x) : ind p ≤ x := by
  unfold ind
  split_ifs with hp
  · exact h1 hp
  · exact h0
theorem ind_congr {p q : Prop} (h : p ↔ q) : ind p = ind q := by
  rw [h]

variable {δ : ℝ}

theorem ex_empty (f : Finset ℕ → ℝ) : ex δ ∅ f = f ∅ := by
  simp [ex]

theorem ex_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : Finset ℕ → ℝ) :
    ex δ (insert a S) f = (1 - δ) * ex δ S f + δ * ex δ S (fun T => f (insert a T)) := by
  unfold ex
  rw [sum_powerset_insert ha, card_insert_of_notMem ha, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have := card_le_card (mem_powerset.mp hT)
    rw [show #S + 1 - #T = (#S - #T) + 1 by omega, pow_succ]
    ring
  · refine sum_congr rfl fun T hT => ?_
    have hT' : a ∉ T := fun h => ha (mem_powerset.mp hT h)
    rw [card_insert_of_notMem hT', show #S + 1 - (#T + 1) = #S - #T by omega, pow_succ]
    ring

theorem ex_congr {S : Finset ℕ} {f g : Finset ℕ → ℝ} (h : ∀ T ⊆ S, f T = g T) :
    ex δ S f = ex δ S g := by
  unfold ex
  exact sum_congr rfl fun T hT => by rw [h T (mem_powerset.mp hT)]

theorem ex_const (S : Finset ℕ) (c : ℝ) : ex δ S (fun _ => c) = c := by
  induction S using Finset.induction_on with
  | empty => simp [ex_empty]
  | insert a S ha ih => rw [ex_insert ha, ih]; ring

theorem ex_add (S : Finset ℕ) (f g : Finset ℕ → ℝ) :
    ex δ S (fun T => f T + g T) = ex δ S f + ex δ S g := by
  unfold ex
  rw [← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem ex_mul_left (S : Finset ℕ) (c : ℝ) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => c * f T) = c * ex δ S f := by
  unfold ex
  rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring

theorem ex_one_sub (S : Finset ℕ) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => 1 - f T) = 1 - ex δ S f := by
  rw [show (1 : ℝ) - ex δ S f = ex δ S (fun _ => 1) - ex δ S f by rw [ex_const]]
  unfold ex
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem ex_sum {ι : Type*} (S : Finset ℕ) (I : Finset ι) (f : ι → Finset ℕ → ℝ) :
    ex δ S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, ex δ S (f i) := by
  unfold ex
  simp only [mul_sum]
  rw [sum_comm]

theorem ex_mono (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {S : Finset ℕ} {f g : Finset ℕ → ℝ}
    (h : ∀ T ⊆ S, f T ≤ g T) : ex δ S f ≤ ex δ S g := by
  unfold ex
  refine sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (h T (mem_powerset.mp hT)) ?_
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

theorem ex_union {A B : Finset ℕ} (hAB : Disjoint A B) (f : Finset ℕ → ℝ) :
    ex δ (A ∪ B) f = ex δ A (fun T => ex δ B (fun U => f (T ∪ U))) := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp [ex_empty]
  | insert a A ha ih =>
    have haB : a ∉ B := fun h => disjoint_left.mp hAB (mem_insert_self a A) h
    have hAB' : Disjoint A B := disjoint_of_subset_left (subset_insert a A) hAB
    have haU : a ∉ A ∪ B := by simp [ha, haB]
    rw [insert_union, ex_insert haU, ex_insert ha, ih hAB', ih hAB']
    simp only [insert_union]

theorem ex_split {A S : Finset ℕ} (hA : A ⊆ S) (f g : Finset ℕ → ℝ) :
    ex δ S (fun T => f (T ∩ A) * g (T \ A)) = ex δ A f * ex δ (S \ A) g := by
  have hd : Disjoint A (S \ A) := disjoint_sdiff
  conv_lhs => rw [← union_sdiff_of_subset hA]
  rw [ex_union hd]
  have e : ∀ T ⊆ A, ex δ (S \ A) (fun U => f ((T ∪ U) ∩ A) * g ((T ∪ U) \ A)) =
      f T * ex δ (S \ A) g := by
    intro T hT
    rw [← ex_mul_left]
    refine ex_congr fun U hU => ?_
    have e1 : (T ∪ U) ∩ A = T := by
      ext x
      have h1 := @hT x
      have h2 := @hU x
      simp only [mem_inter, mem_union, mem_sdiff] at *
      tauto
    have e2 : (T ∪ U) \ A = U := by
      ext x
      have h1 := @hT x
      have h2 := @hU x
      simp only [mem_union, mem_sdiff] at *
      tauto
    rw [e1, e2]
  rw [ex_congr e]
  have := ex_mul_left (δ := δ) A (ex δ (S \ A) g) f
  rw [mul_comm, ← this]
  congr 1
  funext T
  ring

theorem ex_restrict {A S : Finset ℕ} (hA : A ⊆ S) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => f (T ∩ A)) = ex δ A f := by
  have h := ex_split (δ := δ) hA f (fun _ => 1)
  simp only [mul_one, ex_const] at h
  exact h

theorem ex_prod {ι : Type*} (J : Finset ι) (A : ι → Finset ℕ) (g : ι → Finset ℕ → ℝ)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) (S : Finset ℕ)
    (hS : ∀ j ∈ J, A j ⊆ S) :
    ex δ S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, ex δ (A j) (g j) := by
  classical
  revert hd S
  induction J using Finset.induction_on with
  | empty => intro _ S _; simp [ex_const]
  | insert j J hj ih =>
    intro hd S hS
    have hdj : ∀ i ∈ J, Disjoint (A i) (A j) := fun i hi =>
      hd i (mem_insert_of_mem hi) j (mem_insert_self j J) (fun h => hj (h ▸ hi))
    have hd' : ∀ i ∈ J, ∀ k ∈ J, i ≠ k → Disjoint (A i) (A k) := fun i hi k hk =>
      hd i (mem_insert_of_mem hi) k (mem_insert_of_mem hk)
    have hS' : ∀ i ∈ J, A i ⊆ S \ A j := by
      intro i hi x hx
      exact mem_sdiff.mpr ⟨hS i (mem_insert_of_mem hi) hx, fun hxj => disjoint_left.mp (hdj i hi) hx hxj⟩
    have e : ∀ T ⊆ S, ∏ i ∈ insert j J, g i (T ∩ A i) =
        g j (T ∩ A j) * ∏ i ∈ J, g i ((T \ A j) ∩ A i) := by
      intro T _
      rw [prod_insert hj]
      congr 1
      refine prod_congr rfl fun i hi => ?_
      congr 1
      ext x
      simp only [mem_inter, mem_sdiff]
      constructor
      · rintro ⟨hxT, hxi⟩
        exact ⟨⟨hxT, fun hxj => disjoint_left.mp (hdj i hi) hxi hxj⟩, hxi⟩
      · rintro ⟨⟨hxT, _⟩, hxi⟩
        exact ⟨hxT, hxi⟩
    rw [ex_congr e, ex_split (hS j (mem_insert_self j J)) (g j) (fun U => ∏ i ∈ J, g i (U ∩ A i)),
      ih hd' (S \ A j) hS', prod_insert hj]

theorem condProbAt_eq {n i₀ : ℕ} (hi : i₀ < n) (A : Finset ℕ → Prop) :
    condProbAt n δ i₀ A = ex δ ((Finset.range n).erase i₀) (fun U => ind (A (insert i₀ U))) := by
  have hmem : i₀ ∈ range n := mem_range.mpr hi
  have hnot : i₀ ∉ (range n).erase i₀ := notMem_erase _ _
  have hcard : #((range n).erase i₀) = n - 1 := by rw [card_erase_of_mem hmem, card_range]
  unfold condProbAt ex
  conv_lhs => rw [← insert_erase hmem]
  rw [sum_powerset_insert hnot, sum_eq_zero, zero_add]
  · refine sum_congr rfl fun U hU => ?_
    have hU' : i₀ ∉ U := fun h => hnot (mem_powerset.mp hU h)
    rw [card_insert_of_notMem hU', hcard]
    unfold ind
    beta_reduce
    by_cases hA : A (insert i₀ U)
    · rw [if_pos ⟨mem_insert_self _ _, hA⟩, if_pos hA, Nat.add_sub_cancel, mul_one,
        show n - (#U + 1) = n - 1 - #U by omega]
    · rw [if_neg (fun h => hA h.2), if_neg hA, mul_zero]
  · intro T hT
    exact if_neg (fun h => hnot (mem_powerset.mp hT h.1))

theorem ex_contains {Q B : Finset ℕ} (hQ : Q ⊆ B) :
    ex δ B (fun T => ind (Q ⊆ T)) = δ ^ Q.card := by
  have e : ex δ B (fun T => ind (Q ⊆ T)) = ex δ B (fun T => ind (Q ⊆ T ∩ Q)) :=
    ex_congr fun T _ => ind_congr (by simp [subset_inter_iff])
  rw [e, ex_restrict hQ (fun T => ind (Q ⊆ T))]
  unfold ex
  rw [sum_eq_single Q]
  · beta_reduce
    rw [ind_pos subset_rfl]
    simp
  · intro T hT hne
    beta_reduce
    rw [ind_neg, mul_zero]
    exact fun h => hne (subset_antisymm (mem_powerset.mp hT) h)
  · intro h
    exact absurd (mem_powerset_self Q) h

theorem tail_le_choose (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {B : Finset ℕ} {L : ℕ} (hB : B.card ≤ L) (K : ℕ) :
    ex δ B (fun T => ind (K ≤ T.card)) ≤ (L.choose K : ℝ) * δ ^ K := by
  have hpt : ∀ T ⊆ B, ind (K ≤ #T) ≤ ∑ Q ∈ B.powersetCard K, ind (Q ⊆ T) := by
    intro T hT
    refine ind_le (sum_nonneg fun _ _ => ind_nonneg _) fun hK => ?_
    obtain ⟨Q, hQT, hQ⟩ := Finset.exists_subset_card_eq hK
    have hQB : Q ∈ B.powersetCard K := mem_powersetCard.mpr ⟨hQT.trans hT, hQ⟩
    calc (1 : ℝ) = ind (Q ⊆ T) := (ind_pos hQT).symm
      _ ≤ _ := single_le_sum (f := fun Q => ind (Q ⊆ T)) (fun _ _ => ind_nonneg _) hQB
  calc ex δ B (fun T => ind (K ≤ #T))
      ≤ ex δ B (fun T => ∑ Q ∈ B.powersetCard K, ind (Q ⊆ T)) := ex_mono h0 h1 hpt
    _ = ∑ Q ∈ B.powersetCard K, ex δ B (fun T => ind (Q ⊆ T)) :=
      ex_sum _ _ (fun Q T => ind (Q ⊆ T))
    _ = ∑ Q ∈ B.powersetCard K, δ ^ K := sum_congr rfl fun Q hQ => by
      rw [ex_contains (mem_powersetCard.mp hQ).1, (mem_powersetCard.mp hQ).2]
    _ = ((#B).choose K : ℝ) * δ ^ K := by rw [sum_const, card_powersetCard, nsmul_eq_mul]
    _ ≤ (L.choose K : ℝ) * δ ^ K :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose K hB) (pow_nonneg h0 _)

theorem tail_eq (B : Finset ℕ) (K : ℕ) :
    ex δ B (fun T => ind (K ≤ T.card)) = binUpper B.card δ K := by
  unfold ex binUpper
  have hs := sum_powerset_apply_card (fun m => δ ^ m * (1 - δ) ^ (#B - m) * ind (K ≤ m)) (x := B)
  rw [hs]
  have hI : Icc K #B = (range (#B + 1)).filter (fun m => K ≤ m) := by
    ext m
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [hI, sum_filter]
  refine sum_congr rfl fun m _ => ?_
  unfold ind
  split_ifs
  · rw [nsmul_eq_mul]
    ring
  · simp

theorem tail_le_binUpper (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A : Finset ℕ} {G : ℕ} (hA : A.card ≤ G)
    (K : ℕ) : ex δ A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by
  obtain ⟨A', hAA', hA'⟩ := Infinite.exists_superset_card_eq A G hA
  calc ex δ A (fun T => ind (K ≤ #T)) = ex δ A' (fun T => ind (K ≤ #(T ∩ A))) :=
      (ex_restrict hAA' (fun T => ind (K ≤ #T))).symm
    _ ≤ ex δ A' (fun T => ind (K ≤ #T)) := ex_mono h0 h1 fun T _ =>
      ind_le (ind_nonneg _) fun h => (ind_pos (le_trans h (card_le_card inter_subset_left))).ge
    _ = binUpper G δ K := by rw [tail_eq, hA']

theorem windows_le (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (n i₀ L K K' : ℕ) (hK : K' ≤ K) (b : ℝ)
    (hb : ∀ A : Finset ℕ, A.card ≤ L → ex δ A (fun T => ind (K' ≤ T.card)) ≤ b) :
    ex δ ((Finset.range n).erase i₀)
      (fun U => ind (¬ ∀ i < n, (insert i₀ U ∩ window n i L).card ≤ K)) ≤ n * b := by
  have hpt : ∀ U ⊆ (range n).erase i₀, ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i L) ≤ K) ≤
      ∑ i ∈ range n, ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀))) := by
    intro U hU
    refine ind_le (sum_nonneg fun _ _ => ind_nonneg _) fun hn => ?_
    push Not at hn
    obtain ⟨i, hi, hgt⟩ := hn
    have e : U ∩ (window n i L ∩ (range n).erase i₀) = U ∩ window n i L := by
      ext x
      simp only [mem_inter]
      constructor
      · rintro ⟨a, b, _⟩
        exact ⟨a, b⟩
      · rintro ⟨a, b⟩
        exact ⟨a, b, hU a⟩
    have hc : #(insert i₀ U ∩ window n i L) ≤ #(U ∩ window n i L) + 1 :=
      calc #(insert i₀ U ∩ window n i L) ≤ #(insert i₀ (U ∩ window n i L)) :=
          card_le_card fun x hx => by
            simp only [mem_inter, mem_insert] at hx ⊢
            tauto
        _ ≤ _ := card_insert_le _ _
    have hK'' : K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀)) := by rw [e]; omega
    calc (1 : ℝ) = ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀))) := (ind_pos hK'').symm
      _ ≤ _ := single_le_sum (f := fun i => ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀))))
        (fun _ _ => ind_nonneg _) (mem_range.mpr hi)
  calc _ ≤ ex δ ((range n).erase i₀)
        (fun U => ∑ i ∈ range n, ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀)))) :=
      ex_mono h0 h1 hpt
    _ = ∑ i ∈ range n, ex δ ((range n).erase i₀)
        (fun U => ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀)))) :=
      ex_sum _ _ (fun i U => ind (K' ≤ #(U ∩ (window n i L ∩ (range n).erase i₀))))
    _ = ∑ i ∈ range n, ex δ (window n i L ∩ (range n).erase i₀) (fun T => ind (K' ≤ #T)) :=
      sum_congr rfl fun i _ => ex_restrict inter_subset_right (fun T => ind (K' ≤ #T))
    _ ≤ ∑ i ∈ range n, b := sum_le_sum fun i _ => hb _ (le_trans (card_le_card inter_subset_left)
        (by unfold window; exact card_image_le.trans (card_range L).le))
    _ = n * b := by rw [sum_const, card_range, nsmul_eq_mul]

def tile (r u s : ℕ) : Finset ℕ :=
  Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))

theorem cell_subset {r u s c : ℕ} (hc : c ≤ 6 * r + 1) : cell r u s c ⊆ tile r u s := by
  intro x hx
  simp only [cell, tile, mem_Ico] at hx ⊢
  have : c * u ≤ (6 * r + 1) * u := Nat.mul_le_mul_right u hc
  constructor <;> nlinarith [hx.1, hx.2]

theorem cell_card {r u s c : ℕ} (hc : 1 ≤ c) : (cell r u s c).card = u := by
  unfold cell
  rw [Nat.card_Ico]
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (c + 1) * u = c * u + u by ring, ← add_assoc, Nat.add_sub_cancel_left]

theorem ico_disjoint {a m i j : ℕ} (hij : i ≠ j) :
    Disjoint (Finset.Ico (a + i * m) (a + (i + 1) * m)) (Finset.Ico (a + j * m) (a + (j + 1) * m)) := by
  rw [disjoint_left]
  intro x hx hx'
  simp only [mem_Ico] at hx hx'
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have : (i + 1) * m ≤ j * m := Nat.mul_le_mul_right m h
    omega
  · have : (j + 1) * m ≤ i * m := Nat.mul_le_mul_right m h
    omega

theorem tile_disjoint {r u s s' : ℕ} (h : s ≠ s') : Disjoint (tile r u s) (tile r u s') := by
  have := ico_disjoint (a := 0) (m := (6 * r + 1) * u) h
  simpa [tile] using this

theorem ex_isEmpty (C : Finset ℕ) : ex δ C (fun V => ind (V = ∅)) = (1 - δ) ^ C.card := by
  unfold ex
  rw [sum_eq_single ∅]
  · simp [ind]
  · intro T _ hne
    beta_reduce
    rw [ind_neg hne, mul_zero]
  · intro h
    exact absurd (empty_mem_powerset C) h

theorem ex_single_even (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (a u : ℕ) :
    ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1) ≤
      ex δ (Finset.Ico a (a + u)) (fun V => ind (∃ x, V = {x} ∧ Even x)) := by
  have hIc : #(Ico a (a + u)) = u := by rw [Nat.card_Ico]; omega
  have hinj : Function.Injective (fun k => ({a + a % 2 + 2 * k} : Finset ℕ)) := by
    intro k₁ k₂ h
    have := singleton_inj.mp h
    omega
  have hPc : #((range (u / 2)).image (fun k => ({a + a % 2 + 2 * k} : Finset ℕ))) = u / 2 := by
    rw [card_image_of_injective _ hinj, card_range]
  have hPsub : (range (u / 2)).image (fun k => ({a + a % 2 + 2 * k} : Finset ℕ)) ⊆ (Ico a (a + u)).powerset := by
    intro V hV
    rw [mem_image] at hV
    obtain ⟨k, hk, rfl⟩ := hV
    rw [mem_powerset, singleton_subset_iff, mem_Ico]
    rw [mem_range] at hk
    omega
  have hw : ∀ V ∈ (range (u / 2)).image (fun k => ({a + a % 2 + 2 * k} : Finset ℕ)),
      δ ^ #V * (1 - δ) ^ (#(Ico a (a + u)) - #V) * ind (∃ x, V = {x} ∧ Even x) = δ * (1 - δ) ^ (u - 1) := by
    intro V hV
    rw [mem_image] at hV
    obtain ⟨k, _, rfl⟩ := hV
    rw [card_singleton, hIc, ind_pos ⟨_, rfl, Nat.even_iff.mpr (by omega)⟩]
    ring
  unfold ex
  beta_reduce
  calc ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)
      = ∑ V ∈ (range (u / 2)).image (fun k => ({a + a % 2 + 2 * k} : Finset ℕ)),
          δ ^ #V * (1 - δ) ^ (#(Ico a (a + u)) - #V) * ind (∃ x, V = {x} ∧ Even x) := by
        rw [sum_congr rfl hw, sum_const, hPc, nsmul_eq_mul]
        ring
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hPsub fun V _ _ =>
        mul_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)) (ind_nonneg _)

theorem prod_alternate (a b : ℝ) (m : ℕ) :
    ∏ c ∈ Finset.range (2 * m + 1), (if Even c then a else b) = a ^ (m + 1) * b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ¬ Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    have h2 : Even (2 * m + 1 + 1) := ⟨m + 1, by ring⟩
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      if_neg h1, if_pos h2]
    ring

theorem marked_ge (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (r u s : ℕ) :
    markedBound δ r u ≤ ex δ (tile r u s) (fun T => ind (Marked T r u s)) := by
  have hm : 6 * r + 1 = 2 * (3 * r) + 1 := by ring
  have hcell : ∀ c, cell r u s (c + 1) =
      Ico (s * ((6 * r + 1) * u) + c * u) (s * ((6 * r + 1) * u) + c * u + u) := by
    intro c
    unfold cell
    rw [Nat.add_sub_cancel]
    congr 1
    ring
  have hX : 0 ≤ ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) h0) (pow_nonneg (by linarith) _)
  have hP0 : 0 ≤ (1 - δ) ^ u := pow_nonneg (by linarith) _
  have hind : ∀ (c' : ℕ) (V : Finset ℕ),
      0 ≤ (if Even c' then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x)) ∧
        (if Even c' then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x)) ≤ 1 := by
    intro c' V
    split_ifs
    · exact ⟨ind_nonneg _, ind_le_one _⟩
    · exact ⟨ind_nonneg _, ind_le_one _⟩
  have hpt : ∀ T ⊆ tile r u s, ∏ c' ∈ range (6 * r + 1),
      (if Even c' then ind (T ∩ cell r u s (c' + 1) = ∅)
        else ind (∃ x, T ∩ cell r u s (c' + 1) = {x} ∧ Even x)) ≤ ind (Marked T r u s) := by
    intro T _
    by_cases hM : Marked T r u s
    · rw [ind_pos hM]
      exact prod_le_one (fun c' _ => (hind c' _).1) (fun c' _ => (hind c' _).2)
    · rw [ind_neg hM]
      refine le_of_eq (prod_eq_zero_iff.mpr ?_)
      by_contra hall
      push Not at hall
      apply hM
      intro c hc1 hc2
      have h := hall (c - 1) (by rw [mem_range]; omega)
      have hcc : c - 1 + 1 = c := by omega
      rw [hcc] at h
      constructor
      · intro hodd
        have he : Even (c - 1) := by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨k, by omega⟩
        rw [if_pos he] at h
        by_contra hne
        exact h (ind_neg hne)
      · intro hev
        have he : ¬ Even (c - 1) := by
          rintro ⟨k, hk⟩
          obtain ⟨k', hk'⟩ := hev
          omega
        rw [if_neg he] at h
        by_contra hne
        exact h (ind_neg hne)
  calc markedBound δ r u
      = ∏ c' ∈ range (6 * r + 1),
          (if Even c' then (1 - δ) ^ u else ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) := by
        unfold markedBound
        rw [hm, prod_alternate]
    _ ≤ ∏ c' ∈ range (6 * r + 1), ex δ (cell r u s (c' + 1))
          (fun V => if Even c' then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x)) := by
        refine prod_le_prod (fun c' _ => ?_) (fun c' _ => ?_)
        · split_ifs
          · exact hP0
          · exact hX
        · by_cases he : Even c'
          · simp only [if_pos he]
            exact le_of_eq (by rw [ex_isEmpty, cell_card (c := c' + 1) (by omega)])
          · simp only [if_neg he]
            rw [hcell]
            exact ex_single_even h0 h1 _ u
    _ = ex δ (tile r u s) (fun T => ∏ c' ∈ range (6 * r + 1),
          (if Even c' then ind (T ∩ cell r u s (c' + 1) = ∅)
            else ind (∃ x, T ∩ cell r u s (c' + 1) = {x} ∧ Even x))) := by
        refine (ex_prod (range (6 * r + 1)) (fun c' => cell r u s (c' + 1))
          (fun c' V => if Even c' then ind (V = ∅) else ind (∃ x, V = {x} ∧ Even x)) ?_ (tile r u s) ?_).symm
        · intro i _ j _ hij
          show Disjoint (cell r u s (i + 1)) (cell r u s (j + 1))
          rw [hcell, hcell]
          have := ico_disjoint (a := s * ((6 * r + 1) * u)) (m := u) hij
          convert this using 2 <;> ring
        · intro c' hc'
          rw [mem_range] at hc'
          exact cell_subset (c := c' + 1) (by omega)
    _ ≤ _ := ex_mono h0 h1 hpt

theorem marked_congr {T T' : Finset ℕ} {r u s : ℕ} (h : T ∩ tile r u s = T' ∩ tile r u s)
    (hM : Marked T r u s) : Marked T' r u s := by
  intro c hc1 hc2
  have hsub := cell_subset (r := r) (u := u) (s := s) hc2
  have e : T ∩ cell r u s c = T' ∩ cell r u s c := by
    rw [← inter_eq_right.mpr hsub, ← inter_assoc, ← inter_assoc, h]
  rw [← e]
  exact hM c hc1 hc2

theorem tiles_le (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {n r u M₀ i₀ : ℕ} (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) :
    ex δ ((Finset.range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀)) ≤
      n * (1 - markedBound δ r u) ^ M₀ := by
  obtain ⟨N, hN⟩ : ∃ N, N = n / ((6 * r + 1) * u) := ⟨_, rfl⟩
  have hm1 : 1 ≤ (6 * r + 1) * u := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hMN : M₀ + 1 ≤ N := by rw [hN, Nat.le_div_iff_mul_le (by omega)]; exact hn
  have hNn : N ≤ n := hN ▸ Nat.div_le_self _ _
  have hNm : N * ((6 * r + 1) * u) ≤ n := hN ▸ Nat.div_mul_le_self _ _
  have htinj : ∀ s₀ j₁ j₂, j₁ < N → j₂ < N → (s₀ + j₁) % N = (s₀ + j₂) % N → j₁ = j₂ := by
    intro s₀ j₁ j₂ h1 h2 h
    have := Nat.ModEq.add_left_cancel' s₀ h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  have htlt : ∀ s₀ j, (s₀ + j) % N < N := fun s₀ j => Nat.mod_lt _ (by omega)
  have htile : ∀ t < N, tile r u t ⊆ range n := by
    intro t ht x hx
    simp only [tile, mem_Ico] at hx
    rw [mem_range]
    have h1 : (t + 1) * ((6 * r + 1) * u) ≤ N * ((6 * r + 1) * u) := Nat.mul_le_mul_right _ ht
    linarith [hx.2]
  have hgood : ∀ s₀, M₀ ≤ #((range (M₀ + 1)).filter (fun j => i₀ ∉ tile r u ((s₀ + j) % N))) := by
    intro s₀
    have hbad : #((range (M₀ + 1)).filter (fun j => ¬ i₀ ∉ tile r u ((s₀ + j) % N))) ≤ 1 := by
      refine card_le_one.mpr fun j₁ hj₁ j₂ hj₂ => ?_
      rw [mem_filter, mem_range, not_not] at hj₁ hj₂
      by_contra hne
      have hne' : (s₀ + j₁) % N ≠ (s₀ + j₂) % N := fun h => hne (htinj s₀ j₁ j₂ (by omega) (by omega) h)
      exact disjoint_left.mp (tile_disjoint hne') hj₁.2 hj₂.2
    have := card_filter_add_card_filter_not (s := range (M₀ + 1))
      (p := fun j => i₀ ∉ tile r u ((s₀ + j) % N))
    rw [card_range] at this
    omega
  choose J hJsub hJcard using fun s₀ => Finset.exists_subset_card_eq (hgood s₀)
  have hJ : ∀ s₀, ∀ j ∈ J s₀, j < M₀ + 1 ∧ i₀ ∉ tile r u ((s₀ + j) % N) := by
    intro s₀ j hj
    have := hJsub s₀ hj
    rw [mem_filter, mem_range] at this
    exact this
  have hfac : ∀ p : Prop, 0 ≤ 1 - ind p := fun p => by linarith [ind_le_one p]
  have hpt : ∀ U ⊆ (range n).erase i₀, ind (¬ CondTiles n (insert i₀ U) r u M₀) ≤
      ∑ s₀ ∈ range N, ∏ j ∈ J s₀,
        (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N))) := by
    intro U _
    refine ind_le (sum_nonneg fun s₀ _ => prod_nonneg fun j _ => hfac _) fun hct => ?_
    unfold CondTiles at hct
    rw [← hN] at hct
    push Not at hct
    obtain ⟨s₀, hs₀, hall⟩ := hct
    have hone : ∏ j ∈ J s₀,
        (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N))) = 1 := by
      refine prod_eq_one fun j hj => ?_
      obtain ⟨hjM, hji⟩ := hJ s₀ j hj
      rw [ind_neg, sub_zero]
      intro hM
      apply hall j (by omega)
      refine marked_congr ?_ hM
      ext x
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨⟨hxU, hxt⟩, _⟩
        exact ⟨Or.inr hxU, hxt⟩
      · rintro ⟨hx | hxU, hxt⟩
        · exact absurd (hx ▸ hxt) hji
        · exact ⟨⟨hxU, hxt⟩, hxt⟩
    calc (1 : ℝ) = _ := hone.symm
      _ ≤ _ := single_le_sum (f := fun s₀ => ∏ j ∈ J s₀,
          (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N))))
        (fun s₀ _ => prod_nonneg fun j _ => hfac _) (mem_range.mpr hs₀)
  have hex1 : ∀ t, ex δ (tile r u t) (fun T => ind (Marked T r u t)) ≤ 1 := fun t =>
    (ex_mono h0 h1 fun T _ => ind_le_one _).trans (le_of_eq (ex_const _ _))
  have hmb1 : 0 ≤ 1 - markedBound δ r u := by linarith [marked_ge h0 h1 r u 0, hex1 0]
  calc ex δ ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀))
      ≤ ex δ ((range n).erase i₀) (fun U => ∑ s₀ ∈ range N, ∏ j ∈ J s₀,
          (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N)))) := ex_mono h0 h1 hpt
    _ = ∑ s₀ ∈ range N, ex δ ((range n).erase i₀) (fun U => ∏ j ∈ J s₀,
          (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N)))) :=
        ex_sum _ _ (fun s₀ U => ∏ j ∈ J s₀,
          (1 - ind (Marked (U ∩ tile r u ((s₀ + j) % N)) r u ((s₀ + j) % N))))
    _ = ∑ s₀ ∈ range N, ∏ j ∈ J s₀, ex δ (tile r u ((s₀ + j) % N))
          (fun V => 1 - ind (Marked V r u ((s₀ + j) % N))) := by
        refine sum_congr rfl fun s₀ _ => ?_
        refine ex_prod (J s₀) (fun j => tile r u ((s₀ + j) % N))
          (fun j V => 1 - ind (Marked V r u ((s₀ + j) % N))) ?_ _ ?_
        · intro i hi k hk hik
          refine tile_disjoint fun h => hik (htinj s₀ i k ?_ ?_ h)
          · have := (hJ s₀ i hi).1
            omega
          · have := (hJ s₀ k hk).1
            omega
        · intro j hj x hx
          rw [mem_erase]
          exact ⟨fun h => (hJ s₀ j hj).2 (h ▸ hx), htile _ (htlt s₀ j) hx⟩
    _ ≤ ∑ s₀ ∈ range N, (1 - markedBound δ r u) ^ M₀ := by
        refine sum_le_sum fun s₀ _ => ?_
        calc _ ≤ ∏ j ∈ J s₀, (1 - markedBound δ r u) := by
              refine prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
              · rw [ex_one_sub]
                linarith [hex1 ((s₀ + j) % N)]
              · rw [ex_one_sub]
                linarith [marked_ge h0 h1 r u ((s₀ + j) % N)]
          _ = _ := by rw [prod_const, hJcard]
    _ = N * (1 - markedBound δ r u) ^ M₀ := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ n * (1 - markedBound δ r u) ^ M₀ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hNn) (pow_nonneg hmb1 _)

theorem prob_not_good_le : Formalism.G0.TileConditionFailureProbBound := by
  intro n δ L₂ K r u M₀ G' N₁ i₀ h0 h1 _ hu hn hi
  rw [condProbAt_eq hi]
  have hpt : ∀ U ⊆ (range n).erase i₀, ind (¬ GoodOrbitIntervalTileCondition n (insert i₀ U) L₂ K r u M₀ G' N₁) ≤
      ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K) +
        ind (¬ CondTiles n (insert i₀ U) r u M₀) +
        ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁) := by
    intro U _
    have ha := ind_nonneg (¬ ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K)
    have hb := ind_nonneg (¬ CondTiles n (insert i₀ U) r u M₀)
    have hc := ind_nonneg (¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁)
    refine ind_le (by linarith) fun hng => ?_
    by_cases hA : ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K
    · by_cases hB : CondTiles n (insert i₀ U) r u M₀
      · have hC : ¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁ := fun hC => hng ⟨hA, hB, hC⟩
        rw [ind_pos hC]
        linarith
      · rw [ind_pos hB]
        linarith
    · rw [ind_pos hA]
      linarith
  have ha := windows_le h0 h1 n i₀ L₂ K K le_rfl ((L₂.choose K : ℝ) * δ ^ K)
    (fun A hA => tail_le_choose h0 h1 hA K)
  have hb := tiles_le (i₀ := i₀) h0 h1 hu hn
  have hc := windows_le h0 h1 n i₀ G' N₁ (N₁ - 1) (Nat.sub_le _ _) (binUpper G' δ (N₁ - 1))
    (fun A hA => tail_le_binUpper h0 h1 hA (N₁ - 1))
  calc _ ≤ ex δ ((range n).erase i₀) (fun U =>
        ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K) +
          ind (¬ CondTiles n (insert i₀ U) r u M₀) +
          ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁)) := ex_mono h0 h1 hpt
    _ = ex δ ((range n).erase i₀) (fun U => ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K)) +
        ex δ ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀)) +
        ex δ ((range n).erase i₀) (fun U => ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁)) := by
      rw [ex_add, ex_add]
    _ ≤ _ := by linarith

end GlobalTheory.RandomTops
