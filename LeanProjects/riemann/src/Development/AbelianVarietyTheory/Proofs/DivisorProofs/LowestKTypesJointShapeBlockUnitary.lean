import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.LowestTypes

def below (l : List ℚ) (v : ℚ) : ℚ := (l.map fun e => if e < v then (1 : ℚ) else 0).sum

def above (l : List ℚ) (v : ℚ) : ℚ := (l.map fun e => if v < e then (1 : ℚ) else 0).sum

theorem below_cons (e : ℚ) (l : List ℚ) (v : ℚ) :
    below (e :: l) v = (if e < v then 1 else 0) + below l v := by simp [below]

theorem above_cons (e : ℚ) (l : List ℚ) (v : ℚ) :
    above (e :: l) v = (if v < e then 1 else 0) + above l v := by simp [above]

theorem below_append (l m : List ℚ) (v : ℚ) : below (l ++ m) v = below l v + below m v := by
  simp [below]

theorem below_nat (l : List ℚ) (v : ℚ) : ∃ k : ℕ, below l v = k ∧ k ≤ l.length := by
  induction l with
  | nil => exact ⟨0, by simp [below], le_rfl⟩
  | cons e l ih =>
    obtain ⟨k, hk, hl⟩ := ih
    rw [below_cons, hk]
    split_ifs
    · exact ⟨k + 1, by push_cast; ring, by simpa using hl⟩
    · exact ⟨k, by ring, by simp; omega⟩

theorem below_nonneg (l : List ℚ) (v : ℚ) : 0 ≤ below l v := by
  obtain ⟨k, hk, -⟩ := below_nat l v
  rw [hk]; positivity

theorem below_le (l : List ℚ) (v : ℚ) : below l v ≤ l.length := by
  obtain ⟨k, hk, h⟩ := below_nat l v
  rw [hk]; exact_mod_cast h

theorem below_all {l : List ℚ} {v : ℚ} (h : ∀ e ∈ l, e < v) : below l v = l.length := by
  induction l with
  | nil => simp [below]
  | cons e l ih =>
    rw [below_cons, ih fun x hx => h x (List.mem_cons_of_mem _ hx), if_pos (h e List.mem_cons_self)]
    simp; ring

theorem below_none {l : List ℚ} {v : ℚ} (h : ∀ e ∈ l, v ≤ e) : below l v = 0 := by
  induction l with
  | nil => simp [below]
  | cons e l ih =>
    rw [below_cons, ih fun x hx => h x (List.mem_cons_of_mem _ hx),
      if_neg (not_lt.2 (h e List.mem_cons_self))]
    simp

theorem below_mono (l : List ℚ) {u v : ℚ} (h : u ≤ v) : below l u ≤ below l v := by
  induction l with
  | nil => simp [below]
  | cons e l ih =>
    rw [below_cons, below_cons]
    split_ifs with h1 h2 <;> linarith

theorem below_add_above (l : List ℚ) (v : ℚ) :
    below l v + above l v + l.count v = l.length := by
  induction l with
  | nil => simp [below, above]
  | cons e l ih =>
    rw [below_cons, above_cons, List.count_cons, List.length_cons]
    push_cast
    rcases lt_trichotomy e v with h | h | h
    · simp [h, h.not_gt, h.ne]; linarith
    · simp [h]; linarith
    · simp [h, h.not_gt, h.ne']; linarith

theorem below_step {l : List ℚ} {u : ℚ} (h : ∀ e ∈ l, ∃ k : ℤ, e = u + k) :
    below l (u + 1) = below l u + l.count u := by
  induction l with
  | nil => simp [below]
  | cons e l ih =>
    rw [below_cons, below_cons, ih fun x hx => h x (List.mem_cons_of_mem _ hx), List.count_cons]
    obtain ⟨k, rfl⟩ := h e List.mem_cons_self
    have h1 : u + k < u + 1 ↔ k < 1 := by
      rw [add_lt_add_iff_left]; exact_mod_cast Iff.rfl
    have h2 : u + k < u ↔ k < 0 := by
      rw [add_lt_iff_neg_left]; exact_mod_cast Iff.rfl
    have h3 : (u + k == u) = true ↔ k = 0 := by simp
    simp only [h1, h2, h3]
    push_cast
    split_ifs <;> first | omega | linarith

theorem below_le_add {l : List ℚ} {θ u v : ℚ} (nd : l.Nodup) (h : ∀ e ∈ l, ∃ k : ℤ, e = θ + k)
    (hu : ∃ k : ℤ, u = θ + k) (hv : ∃ k : ℤ, v = θ + k) (huv : u ≤ v) :
    below l v ≤ below l u + (v - u) := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have key : ∀ n : ℕ, below l (u + n) ≤ below l u + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : below l (u + n + 1) = below l (u + n) + l.count (u + n) :=
        below_step fun e he => by
          obtain ⟨k, hk⟩ := h e he
          exact ⟨k - a - n, by rw [hk, ha]; push_cast; ring⟩
      have h2 : (l.count (u + n) : ℚ) ≤ 1 := by
        exact_mod_cast List.nodup_iff_count_le_one.1 nd (u + n)
      push_cast
      rw [← add_assoc]
      linarith
  have hab : a ≤ b := by
    have : (a : ℚ) ≤ b := by linarith
    exact_mod_cast this
  obtain ⟨n, hn⟩ := Int.le.dest hab
  have : v = u + n := by rw [ha, hb, ← hn]; push_cast; ring
  have h3 := key n
  rw [this]; linarith

theorem sum_getD {p : ℕ} {l : List ℚ} (h : l.length = p) (f : ℚ → ℚ) :
    ∑ i : Fin p, f (l.getD i 0) = (l.map f).sum := by
  subst h
  rw [← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.getD_eq_getElem _ _ i.2]

theorem getD_mem {p : ℕ} {l : List ℚ} (h : l.length = p) (i : Fin p) : l.getD i 0 ∈ l := by
  subst h
  rw [List.getD_eq_getElem _ _ i.2]
  exact List.getElem_mem _

theorem getD_map' {p : ℕ} {l : List ℚ} (h : l.length = p) (f : ℚ → ℚ) (i : Fin p) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  subst h
  rw [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ (by simp), List.getElem_map]

theorem shiftNu_blattner {p q : ℕ} {l₁ l₂ : List ℚ} (h₁ : l₁.length = p) (h₂ : l₂.length = q)
    (nd : (l₁ ++ l₂).Nodup) (c : ℚ) :
    shiftNu c (blattner (ofBlocks l₁ l₂ : Ix p q → ℚ)) =
      ofBlocks (l₁.map fun v => v + below l₂ v - below l₁ v - 1 / 2 + ((p : ℚ) - q) / 2 - c)
        (l₂.map fun v => v + below l₁ v - below l₂ v - 1 / 2 + ((q : ℚ) - p) / 2 + c) := by
  obtain ⟨n1, n2, n3⟩ := List.nodup_append.1 nd
  have e1 := fun v => sum_getD h₁ fun e => if e < v then (1 : ℚ) else 0
  have e2 := fun v => sum_getD h₂ fun e => if e < v then (1 : ℚ) else 0
  have e3 := fun v => sum_getD h₁ fun e => if v < e then (1 : ℚ) else 0
  have e4 := fun v => sum_getD h₂ fun e => if v < e then (1 : ℚ) else 0
  funext a
  rcases a with i | i
  · have hm := getD_mem h₁ i
    have a1 := below_add_above l₁ (l₁.getD i 0)
    have a2 := below_add_above l₂ (l₁.getD i 0)
    rw [List.count_eq_one_of_mem n1 hm, h₁] at a1
    rw [List.count_eq_zero_of_not_mem (fun h => n3 _ hm _ h rfl), h₂] at a2
    simp only [shiftNu, blattner, rhoNC, Finset.card_filter, Fintype.sum_sum_type]
    simp only [sameBlock, ofBlocks, getD_map' h₁, not_true, not_false_iff, true_and, false_and, if_false]
    push_cast
    rw [e1, e2, e3, e4]
    simp only [below, above] at a1 a2 ⊢
    simp only [Finset.sum_const_zero]
    push_cast at a1 a2
    linarith
  · have hm := getD_mem h₂ i
    have a1 := below_add_above l₁ (l₂.getD i 0)
    have a2 := below_add_above l₂ (l₂.getD i 0)
    rw [List.count_eq_one_of_mem n2 hm, h₂] at a2
    rw [List.count_eq_zero_of_not_mem (fun h => n3 _ h _ hm rfl), h₁] at a1
    simp only [shiftNu, blattner, rhoNC, Finset.card_filter, Fintype.sum_sum_type]
    simp only [sameBlock, ofBlocks, getD_map' h₂, not_true, not_false_iff, true_and, false_and, if_false]
    push_cast
    rw [e1, e2, e3, e4]
    simp only [below, above] at a1 a2 ⊢
    simp only [Finset.sum_const_zero]
    push_cast at a1 a2
    linarith

theorem forall_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} (h₁ : l₁.length = p) (h₂ : l₂.length = q)
    (f g : ℚ → ℚ) (R : ℚ → ℚ → Prop) (hf : ∀ v ∈ l₁, R v (f v)) (hg : ∀ v ∈ l₂, R v (g v))
    (a : Ix p q) : R (ofBlocks l₁ l₂ a) (ofBlocks (l₁.map f) (l₂.map g) a) := by
  rcases a with i | i
  · simp only [ofBlocks, getD_map' h₁]; exact hf _ (getD_mem h₁ i)
  · simp only [ofBlocks, getD_map' h₂]; exact hg _ (getD_mem h₂ i)

theorem getD_lt {p : ℕ} {l : List ℚ} (h : l.length = p) (hl : l.Pairwise (· > ·)) {i j : Fin p}
    (hij : i < j) : l.getD j 0 < l.getD i 0 := by
  subst h
  rw [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ j.2]
  exact List.pairwise_iff_getElem.1 hl i j i.2 j.2 hij

theorem isParam_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} (h₁ : l₁.length = p) (h₂ : l₂.length = q)
    (s₁ : l₁.Pairwise (· > ·)) (s₂ : l₂.Pairwise (· > ·)) (nd : (l₁ ++ l₂).Nodup) (t : ℕ)
    (hc : ∀ e ∈ l₁ ++ l₂, ∃ k : ℤ, e = ((t : ℚ) + 1) / 2 + k) :
    IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) := by
  obtain ⟨-, -, n3⟩ := List.nodup_append.1 nd
  have hm : ∀ a : Ix p q, ∃ k : ℤ, ofBlocks l₁ l₂ a = ((t : ℚ) + 1) / 2 + k := by
    rintro (i | i)
    · exact hc _ (List.mem_append_left _ (getD_mem h₁ i))
    · exact hc _ (List.mem_append_right _ (getD_mem h₂ i))
  refine ⟨?_, ?_, fun a => ?_, fun a b => ?_⟩
  · rintro (i | i) (j | j) hij
    · rcases lt_trichotomy i j with h | h | h
      · exact absurd hij (getD_lt h₁ s₁ h).ne'
      · rw [h]
      · exact absurd hij (getD_lt h₁ s₁ h).ne
    · exact absurd hij (n3 _ (getD_mem h₁ i) _ (getD_mem h₂ j))
    · exact absurd hij.symm (n3 _ (getD_mem h₁ j) _ (getD_mem h₂ i))
    · rcases lt_trichotomy i j with h | h | h
      · exact absurd hij (getD_lt h₂ s₂ h).ne'
      · rw [h]
      · exact absurd hij (getD_lt h₂ s₂ h).ne
  · rintro (i | i) (j | j) hij
    · exact getD_lt h₁ s₁ hij
    · exact hij.elim
    · exact hij.elim
    · exact getD_lt h₂ s₂ hij
  · obtain ⟨k, hk⟩ := hm a
    exact ⟨t + 1 + 2 * k, by rw [hk]; push_cast; ring⟩
  · obtain ⟨k, hk⟩ := hm a
    obtain ⟨m, hm⟩ := hm b
    exact ⟨k - m, by rw [hk, hm]; push_cast; ring⟩

theorem exists_pos_part {l : List ℚ} (hs : l.Pairwise (· ≥ ·))
    (h : ∀ v ∈ l, 0 ≤ v ∧ ∃ k : ℤ, v = k) :
    ∃ (a : List ℤ) (m : ℕ), (∀ v ∈ a, 0 < v) ∧ a.Pairwise (· ≥ ·) ∧
      l = a.map (fun v : ℤ => (v : ℚ)) ++ List.replicate m 0 := by
  induction l with
  | nil => exact ⟨[], 0, by simp, by simp, by simp⟩
  | cons e l ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hs
    obtain ⟨h0, k, rfl⟩ := h e List.mem_cons_self
    rcases h0.lt_or_eq with h0 | h0
    · obtain ⟨a, m, a1, a2, a3⟩ := ih h2 fun v hv => h v (List.mem_cons_of_mem _ hv)
      refine ⟨k :: a, m, ?_, List.pairwise_cons.2 ⟨fun v hv => ?_, a2⟩, by rw [a3]; simp⟩
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact_mod_cast h0
        · exact a1 v hv
      · have := h1 (v : ℚ) (by rw [a3]; exact List.mem_append_left _ (List.mem_map_of_mem hv))
        exact_mod_cast this
    · refine ⟨[], l.length + 1, by simp, by simp, ?_⟩
      rw [← h0, List.map_nil, List.nil_append, List.replicate_succ]
      congr 1
      refine List.eq_replicate_iff.2 ⟨rfl, fun v hv => le_antisymm ?_ ?_⟩
      · rw [h0]; exact h1 v hv
      · exact (h v (List.mem_cons_of_mem _ hv)).1

theorem exists_neg_part {l : List ℚ} (hs : l.Pairwise (· ≥ ·))
    (h : ∀ v ∈ l, v ≤ 0 ∧ ∃ k : ℤ, v = k) :
    ∃ (a : List ℤ) (m : ℕ), (∀ v ∈ a, v < 0) ∧ a.Pairwise (· ≥ ·) ∧
      l = List.replicate m 0 ++ a.map (fun v : ℤ => (v : ℚ)) := by
  obtain ⟨a, m, a1, a2, a3⟩ := exists_pos_part (l := (l.map fun v => -v).reverse)
    (by
      rw [List.pairwise_reverse, List.pairwise_map]
      exact hs.imp fun h => neg_le_neg h)
    (by
      intro v hv
      simp only [List.mem_reverse, List.mem_map] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      obtain ⟨h1, k, rfl⟩ := h u hu
      exact ⟨by linarith, -k, by simp⟩)
  refine ⟨(a.map fun v => -v).reverse, m, ?_, ?_, ?_⟩
  · intro v hv
    simp only [List.mem_reverse, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have := a1 u hu
    omega
  · rw [List.pairwise_reverse, List.pairwise_map]
    exact a2.imp fun h => neg_le_neg h
  · have := congrArg (fun x : List ℚ => (x.map fun v => -v).reverse) a3
    simpa [Function.comp_def] using this

theorem jointShape_of_lists {p q r s t : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ}
    {la lb lc ld : List ℚ}
    (sa : la.Pairwise (· ≥ ·)) (sb : lb.Pairwise (· ≥ ·)) (sc : lc.Pairwise (· ≥ ·))
    (sd : ld.Pairwise (· ≥ ·))
    (ha : ∀ v ∈ la, 0 ≤ v ∧ ∃ k : ℤ, v = k) (hb : ∀ v ∈ lb, v ≤ 0 ∧ ∃ k : ℤ, v = k)
    (hc : ∀ v ∈ lc, 0 ≤ v ∧ ∃ k : ℤ, v = k) (hd : ∀ v ∈ ld, v ≤ 0 ∧ ∃ k : ℤ, v = k)
    (hp : p = la.length + lb.length) (hq : q = lc.length + ld.length)
    (hr : r = la.length + ld.length + t) (hs : s = lc.length + lb.length)
    (e : shiftNu (cPair r s) μ = ofBlocks (la ++ lb) (lc ++ ld))
    (e' : shiftNu (cPair p q) μ' = ofBlocks (la ++ List.replicate t 0 ++ ld) (lc ++ lb)) :
    JointShape p q r s μ μ' := by
  obtain ⟨a, ma, a1, a2, rfl⟩ := exists_pos_part sa ha
  obtain ⟨b, mb, b1, b2, rfl⟩ := exists_neg_part sb hb
  obtain ⟨c, mc, c1, c2, rfl⟩ := exists_pos_part sc hc
  obtain ⟨d, md, d1, d2, rfl⟩ := exists_neg_part sd hd
  simp only [List.length_append, List.length_map, List.length_replicate] at hp hq hr hs
  refine ⟨a, b, c, d, a1, c1, b1, d1, a2, b2, c2, d2, by omega, by omega, by omega, by omega,
    ?_, ?_⟩
  · rw [e, show p - a.length - b.length = ma + mb by omega,
      show q - c.length - d.length = mc + md by omega]
    simp only [pad, List.replicate_add, List.map_append, List.map_replicate, List.append_assoc,
      Int.cast_zero]
  · rw [e', show r - a.length - d.length = ma + t + md by omega,
      show s - c.length - b.length = mc + mb by omega]
    simp only [pad, List.replicate_add, List.map_append, List.map_replicate, List.append_assoc,
      Int.cast_zero]

theorem pairwise_map_count {l m : List ℚ} {θ : ℚ} (hs : l.Pairwise (· > ·))
    (h : ∀ e ∈ l, ∃ k : ℤ, e = θ + k) (c : ℚ) :
    (l.map fun v => v + below m v - below l v + c).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  refine hs.imp_of_mem fun {u v} hu hv huv => ?_
  have h1 := below_le_add (hs.imp fun h => h.ne') h (h v hv) (h u hu) huv.le
  have h2 := below_mono m huv.le
  show v + below m v - below l v + c ≤ u + below m u - below l u + c
  linarith

theorem int_count (l m : List ℚ) {θ v c : ℚ} (h : ∃ k : ℤ, v = θ + k) (hc : ∃ k : ℤ, θ + c = k) :
    ∃ k : ℤ, v + below m v - below l v + c = k := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨j, hj⟩ := hc
  obtain ⟨a, ha, -⟩ := below_nat l v
  obtain ⟨b, hb, -⟩ := below_nat m v
  exact ⟨k + j + b - a, by rw [ha, hb]; push_cast; linarith⟩

theorem length_block (t : ℕ) : (block t).length = t := by simp [block]

theorem block_eq (t : ℕ) :
    block t = (List.range t).map fun m : ℕ => ((t : ℚ) - 1) / 2 - (m : ℚ) := by
  simp [block, List.flatMap_singleton', ← List.map_eq_flatMap, Function.comp_def]

theorem mem_block {t : ℕ} {v : ℚ} (h : v ∈ block t) :
    -(((t : ℚ) - 1) / 2) ≤ v ∧ v ≤ ((t : ℚ) - 1) / 2 ∧ ∃ k : ℤ, v = ((t : ℚ) + 1) / 2 + k := by
  simp only [block_eq, List.mem_map, List.mem_range] at h
  obtain ⟨m, hm, rfl⟩ := h
  have h1 : (m : ℚ) + 1 ≤ t := by exact_mod_cast hm
  have h2 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  exact ⟨by linarith, by linarith, -1 - m, by push_cast; ring⟩

theorem block_pairwise (t : ℕ) : (block t).Pairwise (· > ·) := by
  rw [block_eq, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have : (a : ℚ) < b := by exact_mod_cast h
  show _ - (b : ℚ) < _ - (a : ℚ)
  linarith

theorem below_block {t : ℕ} {v : ℚ} (h : v ∈ block t) :
    below (block t) v = v + ((t : ℚ) - 1) / 2 := by
  obtain ⟨h1, h2, h3⟩ := mem_block h
  have nd : (block t).Nodup := (block_pairwise t).imp fun h => h.ne'
  have a1 := below_le_add nd (fun e he => (mem_block he).2.2)
    (u := -(((t : ℚ) - 1) / 2)) ⟨-t, by push_cast; ring⟩ h3 h1
  have a2 := below_le_add nd (fun e he => (mem_block he).2.2)
    (v := ((t : ℚ) + 1) / 2) h3 ⟨0, by simp⟩ (by linarith)
  rw [below_none fun e he => (mem_block he).1] at a1
  rw [below_all fun e he => by linarith [(mem_block he).2.1], length_block] at a2
  linarith

theorem below_le_top {l : List ℚ} {θ v : ℚ} (hs : l.Pairwise (· > ·))
    (h : ∀ e ∈ l, θ ≤ e ∧ ∃ k : ℤ, e = θ + k) (hv : v ∈ l) : below l v ≤ v - θ := by
  have := below_le_add (hs.imp fun h => h.ne') (fun e he => (h e he).2) (u := θ) ⟨0, by simp⟩
    (h v hv).2 (h v hv).1
  rw [below_none fun e he => (h e he).1] at this
  linarith

theorem le_below_bot {l : List ℚ} {t : ℕ} {v : ℚ} (hs : l.Pairwise (· > ·))
    (h : ∀ e ∈ l, e ≤ -(((t : ℚ) + 1) / 2) ∧ ∃ k : ℤ, e = ((t : ℚ) + 1) / 2 + k) (hv : v ∈ l) :
    (l.length : ℚ) - below l v ≤ 1 - ((t : ℚ) + 1) / 2 - v := by
  have := below_le_add (hs.imp fun h => h.ne') (fun e he => (h e he).2)
    (v := 1 - ((t : ℚ) + 1) / 2) (h v hv).2 ⟨-t, by push_cast; ring⟩ (by linarith [(h v hv).1])
  rw [below_all fun e he => by linarith [(h e he).1]] at this
  linarith

theorem lowest_types : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamA' t al be ga de)) ∧ IsParam (lamA al be ga de) ∧ IsParam (lamA' t al be ga de) ∧ (∀ a, (0 < lamA al be ga de a → 0 ≤ shiftNu (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) a) ∧ (lamA al be ga de a < 0 → shiftNu (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) a ≤ 0)) ∧ (∀ c, ((t : ℚ) / 2 < lamA' t al be ga de c → 0 ≤ shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) c) ∧ (lamA' t al be ga de c ≤ (t : ℚ) / 2 → shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) c ≤ 0)) := by
  intro t al be ga de h
  obtain ⟨-, -, sa, sb, sc, sd, nd, hpos, hneg, hco, habs⟩ := h
  have t0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  have ha : ∀ e ∈ al, ((t : ℚ) + 1) / 2 ≤ e ∧ ∃ k : ℤ, e = ((t : ℚ) + 1) / 2 + k := fun e he => by
    have := habs e (by simp [he])
    rw [abs_of_pos (hpos e (by simp [he]))] at this
    exact ⟨this, hco e (by simp [he])⟩
  have hc : ∀ e ∈ ga, ((t : ℚ) + 1) / 2 ≤ e ∧ ∃ k : ℤ, e = ((t : ℚ) + 1) / 2 + k := fun e he => by
    have := habs e (by simp [he])
    rw [abs_of_pos (hpos e (by simp [he]))] at this
    exact ⟨this, hco e (by simp [he])⟩
  have hb : ∀ e ∈ be, e ≤ -(((t : ℚ) + 1) / 2) ∧ ∃ k : ℤ, e = ((t : ℚ) + 1) / 2 + k :=
    fun e he => by
      have := habs e (by simp [he])
      rw [abs_of_neg (hneg e (by simp [he]))] at this
      exact ⟨by linarith, hco e (by simp [he])⟩
  have hd : ∀ e ∈ de, e ≤ -(((t : ℚ) + 1) / 2) ∧ ∃ k : ℤ, e = ((t : ℚ) + 1) / 2 + k :=
    fun e he => by
      have := habs e (by simp [he])
      rw [abs_of_neg (hneg e (by simp [he]))] at this
      exact ⟨by linarith, hco e (by simp [he])⟩
  have hk := @mem_block t
  have nac : ∀ u ∈ al, ∀ v ∈ ga, u ≠ v := fun u hu v hv =>
    (List.nodup_append.1 (List.nodup_append.1 nd).1).2.2 u (by simp [hu]) v hv
  have nbd : ∀ u ∈ be, ∀ v ∈ de, u ≠ v := fun u hu v hv =>
    (List.nodup_append.1 nd).2.2 u (by simp [hu]) v hv
  have s1 : (al ++ be).Pairwise (· > ·) := List.pairwise_append.2 ⟨sa, sb, fun u hu v hv => by
    show v < u; linarith [(ha u hu).1, (hb v hv).1]⟩
  have s2 : (ga ++ de).Pairwise (· > ·) := List.pairwise_append.2 ⟨sc, sd, fun u hu v hv => by
    show v < u; linarith [(hc u hu).1, (hd v hv).1]⟩
  have s3 : (al ++ block t ++ de).Pairwise (· > ·) :=
    List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨sa, block_pairwise t, fun u hu v hv => by
      show v < u; linarith [(ha u hu).1, (hk hv).2.1]⟩, sd, fun u hu v hv => by
      show v < u
      rcases List.mem_append.1 hu with hu | hu
      · linarith [(ha u hu).1, (hd v hv).1]
      · linarith [(hk hu).1, (hd v hv).1]⟩
  have s4 : (ga ++ be).Pairwise (· > ·) := List.pairwise_append.2 ⟨sc, sb, fun u hu v hv => by
    show v < u; linarith [(hc u hu).1, (hb v hv).1]⟩
  have nd1 : ((al ++ be) ++ (ga ++ de)).Nodup := by rwa [← List.append_assoc]
  have nd2 : ((al ++ block t ++ de) ++ (ga ++ be)).Nodup := by
    refine List.nodup_append.2 ⟨s3.imp fun h => h.ne', s4.imp fun h => h.ne', ?_⟩
    intro u hu v hv e
    subst e
    simp only [List.mem_append] at hu hv
    rcases hu with (hu | hu) | hu <;> rcases hv with hv | hv
    · exact nac u hu u hv rfl
    · linarith [(ha u hu).1, (hb u hv).1]
    · linarith [(hk hu).2.1, (hc u hv).1]
    · linarith [(hk hu).1, (hb u hv).1]
    · linarith [(hd u hu).1, (hc u hv).1]
    · exact nbd u hv u hu rfl
  have l1 : (al ++ be).length = al.length + be.length := by simp
  have l2 : (ga ++ de).length = ga.length + de.length := by simp
  have l3 : (al ++ block t ++ de).length = al.length + de.length + t := by
    simp [length_block]; omega
  have l4 : (ga ++ be).length = ga.length + be.length := by simp

  have top : ∀ {v : ℚ}, ((t : ℚ) + 1) / 2 ≤ v → below be v = be.length ∧ below de v = de.length ∧
      below (block t) v = t := fun hv =>
    ⟨below_all fun e he => by linarith [(hb e he).1],
      below_all fun e he => by linarith [(hd e he).1],
      by rw [below_all fun e he => by linarith [(hk he).2.1], length_block]⟩
  have bot : ∀ {v : ℚ}, v ≤ -(((t : ℚ) + 1) / 2) → below al v = 0 ∧ below ga v = 0 ∧
      below (block t) v = 0 := fun hv =>
    ⟨below_none fun e he => by linarith [(ha e he).1],
      below_none fun e he => by linarith [(hc e he).1],
      below_none fun e he => by linarith [(hk he).1]⟩
  have mid : ∀ {v : ℚ}, v ∈ block t → below al v = 0 ∧ below ga v = 0 ∧
      below be v = be.length ∧ below de v = de.length := fun hv =>
    ⟨below_none fun e he => by linarith [(ha e he).1, (hk hv).2.1],
      below_none fun e he => by linarith [(hc e he).1, (hk hv).2.1],
      below_all fun e he => by linarith [(hb e he).1, (hk hv).1],
      below_all fun e he => by linarith [(hd e he).1, (hk hv).1]⟩

  set fa : ℚ → ℚ := fun v => v + below ga v - below al v + -(((t : ℚ) + 1) / 2) with hfa
  set fc : ℚ → ℚ := fun v => v + below al v - below ga v + (((t : ℚ) - 1) / 2) with hfc
  set fb : ℚ → ℚ := fun v => v + below de v - below be v +
    ((be.length : ℚ) - de.length - ((t : ℚ) + 1) / 2) with hfb
  set fd : ℚ → ℚ := fun v => v + below be v - below de v +
    ((de.length : ℚ) - be.length + ((t : ℚ) - 1) / 2) with hfd
  have pa : ∀ v ∈ al, 0 ≤ fa v := fun v hv => by
    have := below_le_top sa ha hv
    have := below_nonneg ga v
    simp only [hfa]; linarith
  have pc : ∀ v ∈ ga, 0 ≤ fc v := fun v hv => by
    have := below_le_top sc hc hv
    have := below_nonneg al v
    simp only [hfc]; linarith
  have pb : ∀ v ∈ be, fb v ≤ 0 := fun v hv => by
    have := le_below_bot sb hb hv
    have := below_le de v
    simp only [hfb]; linarith
  have pd : ∀ v ∈ de, fd v ≤ 0 := fun v hv => by
    have := le_below_bot sd hd hv
    have := below_le be v
    simp only [hfd]; linarith
  have E1 := shiftNu_blattner l1 l2 nd1
    (cPair (al.length + de.length + t) (ga.length + be.length))
  have E2 := shiftNu_blattner l3 l4 nd2 (cPair (al.length + be.length) (ga.length + de.length))
  set F1 : ℚ → ℚ := fun v => v + below (ga ++ de) v - below (al ++ be) v - 1 / 2 +
    (((al.length + be.length : ℕ) : ℚ) - (ga.length + de.length : ℕ)) / 2 -
    cPair (al.length + de.length + t) (ga.length + be.length) with hF1
  set F2 : ℚ → ℚ := fun v => v + below (al ++ be) v - below (ga ++ de) v - 1 / 2 +
    (((ga.length + de.length : ℕ) : ℚ) - (al.length + be.length : ℕ)) / 2 +
    cPair (al.length + de.length + t) (ga.length + be.length) with hF2
  set F3 : ℚ → ℚ := fun v => v + below (ga ++ be) v - below (al ++ block t ++ de) v - 1 / 2 +
    (((al.length + de.length + t : ℕ) : ℚ) - (ga.length + be.length : ℕ)) / 2 -
    cPair (al.length + be.length) (ga.length + de.length) with hF3
  set F4 : ℚ → ℚ := fun v => v + below (al ++ block t ++ de) v - below (ga ++ be) v - 1 / 2 +
    (((ga.length + be.length : ℕ) : ℚ) - (al.length + de.length + t : ℕ)) / 2 +
    cPair (al.length + be.length) (ga.length + de.length) with hF4
  have c1a : ∀ v ∈ al, F1 v = fa v := fun v hv => by
    obtain ⟨x1, x2, x3⟩ := top (ha v hv).1
    simp only [hF1, hfa, below_append, cPair, x1, x2]; push_cast; ring
  have c1b : ∀ v ∈ be, F1 v = fb v := fun v hv => by
    obtain ⟨x1, x2, x3⟩ := bot (hb v hv).1
    simp only [hF1, hfb, below_append, cPair, x1, x2]; push_cast; ring
  have c2c : ∀ v ∈ ga, F2 v = fc v := fun v hv => by
    obtain ⟨x1, x2, x3⟩ := top (hc v hv).1
    simp only [hF2, hfc, below_append, cPair, x1, x2]; push_cast; ring
  have c2d : ∀ v ∈ de, F2 v = fd v := fun v hv => by
    obtain ⟨x1, x2, x3⟩ := bot (hd v hv).1
    simp only [hF2, hfd, below_append, cPair, x1, x2]; push_cast; ring
  have c3a : ∀ v ∈ al, F3 v = fa v := fun v hv => by
    obtain ⟨x1, x2, x3⟩ := top (ha v hv).1
    simp only [hF3, hfa, below_append, cPair, x1, x2, x3]; push_cast; ring
  have c3k : ∀ v ∈ block t, F3 v = 0 := fun v hv => by
    obtain ⟨x1, x2, x3, x4⟩ := mid hv
    simp only [hF3, below_append, cPair, x1, x2, x3, x4, below_block hv]; push_cast; ring
  have c3d : ∀ v ∈ de, F3 v = fd v := fun v hv => by
    obtain ⟨x1, x2, x3⟩ := bot (hd v hv).1
    simp only [hF3, hfd, below_append, cPair, x1, x2, x3]; push_cast; ring
  have c4c : ∀ v ∈ ga, F4 v = fc v := fun v hv => by
    obtain ⟨x1, x2, x3⟩ := top (hc v hv).1
    simp only [hF4, hfc, below_append, cPair, x1, x2, x3]; push_cast; ring
  have c4b : ∀ v ∈ be, F4 v = fb v := fun v hv => by
    obtain ⟨x1, x2, x3⟩ := bot (hb v hv).1
    simp only [hF4, hfb, below_append, cPair, x1, x2, x3]; push_cast; ring
  refine ⟨?_, isParam_ofBlocks l1 l2 s1 s2 nd1 t fun e he => hco e (by rwa [List.append_assoc]),
    isParam_ofBlocks l3 l4 s3 s4 nd2 t fun e he => ?_, fun a => ?_, fun a => ?_⟩
  · refine jointShape_of_lists (t := t) (la := al.map fa) (lb := be.map fb) (lc := ga.map fc)
      (ld := de.map fd) (pairwise_map_count sa (fun e he => (ha e he).2) _)
      (pairwise_map_count sb (fun e he => (hb e he).2) _)
      (pairwise_map_count sc (fun e he => (hc e he).2) _)
      (pairwise_map_count sd (fun e he => (hd e he).2) _)
      (List.forall_mem_map.2 fun v hv => ⟨pa v hv, int_count _ _ (ha v hv).2 ⟨0, by simp⟩⟩)
      (List.forall_mem_map.2 fun v hv => ⟨pb v hv, int_count _ _ (hb v hv).2
        ⟨be.length - de.length, by push_cast; ring⟩⟩)
      (List.forall_mem_map.2 fun v hv => ⟨pc v hv, int_count _ _ (hc v hv).2
        ⟨t, by push_cast; ring⟩⟩)
      (List.forall_mem_map.2 fun v hv => ⟨pd v hv, int_count _ _ (hd v hv).2
        ⟨de.length - be.length + t, by push_cast; ring⟩⟩)
      (by simp) (by simp) (by simp) (by simp) ?_ ?_
    · rw [lamA, E1, List.map_append, List.map_append, List.map_congr_left c1a,
        List.map_congr_left c1b, List.map_congr_left c2c, List.map_congr_left c2d]
    · rw [lamA', E2, List.map_append, List.map_append, List.map_append, List.map_congr_left c3a,
        List.map_congr_left c3k, List.map_congr_left c3d, List.map_congr_left c4c,
        List.map_congr_left c4b, List.map_const', length_block]
  · simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he | he
    exacts [(ha e he).2, (hk he).2.2, (hd e he).2, (hc e he).2, (hb e he).2]
  · rw [lamA, E1]
    refine forall_ofBlocks l1 l2 F1 F2 (fun v w => (0 < v → 0 ≤ w) ∧ (v < 0 → w ≤ 0))
      (fun v hv => ?_) (fun v hv => ?_) a <;> rcases List.mem_append.1 hv with hv | hv
    · exact ⟨fun _ => c1a v hv ▸ pa v hv, fun h => by linarith [(ha v hv).1]⟩
    · exact ⟨fun h => by linarith [(hb v hv).1], fun _ => c1b v hv ▸ pb v hv⟩
    · exact ⟨fun _ => c2c v hv ▸ pc v hv, fun h => by linarith [(hc v hv).1]⟩
    · exact ⟨fun h => by linarith [(hd v hv).1], fun _ => c2d v hv ▸ pd v hv⟩
  · rw [lamA', E2]
    refine forall_ofBlocks l3 l4 F3 F4
      (fun v w => ((t : ℚ) / 2 < v → 0 ≤ w) ∧ (v ≤ (t : ℚ) / 2 → w ≤ 0))
      (fun v hv => ?_) (fun v hv => ?_) a <;> rcases List.mem_append.1 hv with hv | hv
    · rcases List.mem_append.1 hv with hv | hv
      · exact ⟨fun _ => c3a v hv ▸ pa v hv, fun h => by linarith [(ha v hv).1]⟩
      · exact ⟨fun _ => (c3k v hv).ge, fun _ => (c3k v hv).le⟩
    · exact ⟨fun h => by linarith [(hd v hv).1], fun _ => c3d v hv ▸ pd v hv⟩
    · exact ⟨fun _ => c4c v hv ▸ pc v hv, fun h => by linarith [(hc v hv).1]⟩
    · exact ⟨fun h => by linarith [(hb v hv).1], fun _ => c4b v hv ▸ pb v hv⟩

end GlobalTheory.LowestTypes
