import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.WtInterlace

open Finset GlobalTheory.SignedHC

def cnt (p : ℚ → Bool) (A B : Finset ℚ) : ℤ := ((A.filter fun x => p x).card : ℤ) - (B.filter fun x => p x).card

def IsUp (p : ℚ → Bool) : Prop := ∀ a b, a ≤ b → p a = true → p b = true

def Good (lo hi tot : ℤ) (A B : Finset ℚ) : Prop :=
  Disjoint A B ∧ (A.card : ℤ) - B.card = tot ∧ ∀ p, IsUp p → lo ≤ cnt p A B ∧ cnt p A B ≤ hi

theorem Good.union {lo1 hi1 t1 lo2 hi2 t2 lo hi : ℤ} {A1 B1 A2 B2 : Finset ℚ} (h1 : Good lo1 hi1 t1 A1 B1)
    (h2 : Good lo2 hi2 t2 A2 B2) (hsep : ∀ x ∈ A1 ∪ B1, ∀ y ∈ A2 ∪ B2, y < x) (hl1 : lo ≤ lo1) (hh1 : hi1 ≤ hi)
    (hl2 : lo ≤ t1 + lo2) (hh2 : t1 + hi2 ≤ hi) : Good lo hi (t1 + t2) (A1 ∪ A2) (B1 ∪ B2) := by
  obtain ⟨d1, c1, b1⟩ := h1
  obtain ⟨d2, c2, b2⟩ := h2
  have sAA : Disjoint A1 A2 := disjoint_left.2 fun x hx hx' =>
    lt_irrefl x (hsep x (mem_union_left _ hx) x (mem_union_left _ hx'))
  have sBB : Disjoint B1 B2 := disjoint_left.2 fun x hx hx' =>
    lt_irrefl x (hsep x (mem_union_right _ hx) x (mem_union_right _ hx'))
  have sAB : Disjoint A1 B2 := disjoint_left.2 fun x hx hx' =>
    lt_irrefl x (hsep x (mem_union_left _ hx) x (mem_union_right _ hx'))
  have sBA : Disjoint A2 B1 := disjoint_left.2 fun x hx hx' =>
    lt_irrefl x (hsep x (mem_union_right _ hx') x (mem_union_left _ hx))
  refine ⟨?_, ?_, fun p hp => ?_⟩
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨d1, sAB⟩, ⟨sBA, d2⟩⟩
  · rw [card_union_of_disjoint sAA, card_union_of_disjoint sBB]
    push_cast
    linarith
  · have e : cnt p (A1 ∪ A2) (B1 ∪ B2) = cnt p A1 B1 + cnt p A2 B2 := by
      simp only [cnt, filter_union]
      rw [card_union_of_disjoint (disjoint_filter_filter sAA), card_union_of_disjoint (disjoint_filter_filter sBB)]
      push_cast
      ring
    rw [e]
    by_cases hY : ∃ y ∈ A2 ∪ B2, p y = true
    · obtain ⟨y, hy, hpy⟩ := hY
      have hX : ∀ x ∈ A1 ∪ B1, p x = true := fun x hx => hp y x (hsep x hx y hy).le hpy
      have e1 : cnt p A1 B1 = t1 := by
        rw [cnt, filter_true_of_mem fun x hx => hX x (mem_union_left _ hx),
          filter_true_of_mem fun x hx => hX x (mem_union_right _ hx), c1]
      rw [e1]
      have := b2 p hp
      constructor <;> linarith [this.1, this.2]
    · push_neg at hY
      have e2 : cnt p A2 B2 = 0 := by
        rw [cnt, filter_false_of_mem fun x hx => by simpa using hY x (mem_union_left _ hx),
          filter_false_of_mem fun x hx => by simpa using hY x (mem_union_right _ hx)]
        simp
      rw [e2, add_zero]
      have := b1 p hp
      constructor <;> linarith [this.1, this.2]

theorem good_pair {x y : ℚ} (h : x < y) : Good (-1) 0 0 {x} {y} := by
  refine ⟨disjoint_singleton.2 h.ne, by simp, fun p hp => ?_⟩
  simp only [cnt, filter_singleton]
  by_cases hx : p x = true
  · have hy := hp x y h.le hx
    simp [hx, hy]
  · by_cases hy : p y = true <;> simp [hx, hy]

theorem good_single (x : ℚ) : Good 0 1 1 {x} ∅ := by
  refine ⟨disjoint_empty_right _, by simp, fun p _ => ?_⟩
  simp only [cnt, filter_singleton, filter_empty, card_empty]
  by_cases hx : p x = true <;> simp [hx]

theorem good_congr {lo hi t : ℤ} {A B A' B' : Finset ℚ} (h : Good lo hi t A B) (hA : A = A') (hB : B = B') :
    Good lo hi t A' B' := hA ▸ hB ▸ h

theorem block_succ_top (c : ℚ) (n : ℕ) : TPar.block c (n + 1) = {c + (n : ℚ) / 2} ∪ TPar.block (c - 1 / 2) n := by
  ext x
  simp only [mem_union, mem_singleton, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases Nat.eq_zero_or_pos a with rfl | h
    · left; push_cast; ring
    · right; exact ⟨a - 1, by omega, by rw [Nat.cast_sub h]; push_cast; ring⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨0, by omega, by push_cast; ring⟩
    · exact ⟨a + 1, by omega, by push_cast; ring⟩

theorem block_succ_bot (c : ℚ) (n : ℕ) : TPar.block c (n + 1) = TPar.block (c + 1 / 2) n ∪ {c - (n : ℚ) / 2} := by
  ext x
  simp only [mem_union, mem_singleton, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases (Nat.lt_succ_iff.1 ha).eq_or_lt with rfl | h
    · right; push_cast; ring
    · left; exact ⟨a, h, by push_cast; ring⟩
  · rintro (⟨a, ha, rfl⟩ | rfl)
    · exact ⟨a, by omega, by push_cast; ring⟩
    · exact ⟨n, by omega, by push_cast; ring⟩

theorem block_le {c x : ℚ} {n : ℕ} (h : x ∈ TPar.block c n) : x ≤ c + ((n : ℚ) - 1) / 2 := by
  obtain ⟨a, -, rfl⟩ := mem_block.1 h
  have : (0 : ℚ) ≤ a := by positivity
  linarith

theorem block_ge {c x : ℚ} {n : ℕ} (h : x ∈ TPar.block c n) : c - ((n : ℚ) - 1) / 2 ≤ x := by
  obtain ⟨a, ha, rfl⟩ := mem_block.1 h
  have : (a : ℚ) + 1 ≤ n := by exact_mod_cast ha
  linarith

theorem good_blocks : ∀ (n : ℕ) (c : ℚ), Good (-1) 0 0 (TPar.block c n) (TPar.block (c + 1 / 2) n) := by
  intro n
  induction n with
  | zero => intro c; exact ⟨by simp [TPar.block], by simp [TPar.block], fun p _ => by simp [cnt, TPar.block]⟩
  | succ n ih =>
    intro c
    have h := ih (c - 1 / 2)
    rw [sub_add_cancel] at h
    have e1 := block_succ_top c n
    have e2 := block_succ_top (c + 1 / 2) n
    rw [add_sub_cancel_right] at e2
    rw [e1, e2]
    have := (good_pair (x := c + (n : ℚ) / 2) (y := c + 1 / 2 + (n : ℚ) / 2) (by linarith)).union h ?_
      (le_refl _) (le_refl _) (by norm_num) (by norm_num)
    · simpa using this
    · intro x hx y hy
      simp only [mem_union, mem_singleton] at hx
      have hy' : y ≤ c + ((n : ℚ) - 1) / 2 := by
        rcases mem_union.1 hy with hy | hy
        · have := block_le hy; linarith
        · exact block_le hy
      rcases hx with rfl | rfl <;> linarith

end GlobalTheory.WtInterlace

namespace GlobalTheory.WtInterlace

open Finset GlobalTheory.SignedHC

theorem good_empty : Good (-1) 0 0 ∅ ∅ := ⟨disjoint_empty_left _, by simp, fun p _ => by simp [cnt]⟩

theorem good_family (A B : ℕ → Finset ℚ) (lo : ℕ) : ∀ n : ℕ,
    (∀ i, lo ≤ i → i < lo + n → Good (-1) 0 0 (A i) (B i)) →
    (∀ i j, lo ≤ i → i < j → j < lo + n → ∀ x ∈ A i ∪ B i, ∀ y ∈ A j ∪ B j, y < x) →
    Good (-1) 0 0 ((Ico lo (lo + n)).biUnion A) ((Ico lo (lo + n)).biUnion B) := by
  intro n
  induction n with
  | zero => intro _ _; simpa using good_empty
  | succ n ih =>
    intro hg hsep
    have e : Ico lo (lo + (n + 1)) = insert (lo + n) (Ico lo (lo + n)) := by
      ext i; simp only [mem_insert, mem_Ico]; omega
    rw [e, biUnion_insert, biUnion_insert, union_comm (A (lo + n)), union_comm (B (lo + n))]
    have h1 := ih (fun i h1 h2 => hg i h1 (by omega)) (fun i j h1 h2 h3 => hsep i j h1 h2 (by omega))
    have h2 := hg (lo + n) (by omega) (by omega)
    have := h1.union h2 ?_ (le_refl _) (le_refl _) (by norm_num) (by norm_num)
    · simpa using this
    · intro x hx y hy
      have hx' : x ∈ (Ico lo (lo + n)).biUnion (fun i => A i ∪ B i) := by
        rw [biUnion_union]; exact hx
      obtain ⟨i, hi, hx''⟩ := mem_biUnion.1 hx'
      rw [mem_Ico] at hi
      exact hsep i (lo + n) hi.1 hi.2 (by omega) x hx'' y hy

theorem cnt_decide (P : ℚ → Prop) [DecidablePred P] (A B : Finset ℚ) :
    cnt (fun z => decide (P z)) A B = ((A.filter P).card : ℤ) - (B.filter P).card := by
  simp [cnt]

theorem isUp_le (q : ℚ) : IsUp (fun z => decide (q ≤ z)) := fun a b h ha => by
  simp only [decide_eq_true_eq] at ha ⊢; linarith

theorem isUp_lt (q : ℚ) : IsUp (fun z => decide (q < z)) := fun a b h ha => by
  simp only [decide_eq_true_eq] at ha ⊢; linarith

theorem strictInterlace_of_good {A B : Finset ℚ} (h : Good 0 1 1 A B) : StrictInterlace A B := by
  obtain ⟨hd, hc, hb⟩ := h
  rw [strictInterlace_iff]
  refine ⟨hd, card_pos.1 (by omega), fun y hy => ?_, fun y hy => ?_, fun x hx y hy hxy hz => ?_⟩
  · by_contra hne
    push_neg at hne
    have h1 : 0 ≤ ((A.filter fun z => y ≤ z).card : ℤ) - (B.filter fun z => y ≤ z).card := by
      have := (hb _ (isUp_le y)).1; rw [cnt_decide] at this; exact this
    have e1 : A.filter (fun z => y ≤ z) = ∅ := filter_eq_empty_iff.2 fun z hz h' =>
      disjoint_left.1 hd (le_antisymm (hne z hz) h' ▸ hz) hy
    have e2 : 1 ≤ (B.filter (fun z => y ≤ z)).card := card_pos.2 ⟨y, mem_filter.2 ⟨hy, le_rfl⟩⟩
    rw [e1, card_empty] at h1
    omega
  · by_contra hne
    push_neg at hne
    have h1 : ((A.filter fun z => y < z).card : ℤ) - (B.filter fun z => y < z).card ≤ 1 := by
      have := (hb _ (isUp_lt y)).2; rw [cnt_decide] at this; exact this
    have e1 : A.filter (fun z => y < z) = A := filter_true_of_mem fun z hz =>
      lt_of_le_of_ne (hne z hz) fun e => disjoint_left.1 hd (e ▸ hz) hy
    have e2 : B.filter (fun z => y < z) ⊆ B.erase y := fun z hz => by
      rw [mem_filter] at hz; exact mem_erase.2 ⟨hz.2.ne', hz.1⟩
    have e3 := card_le_card e2
    rw [card_erase_of_mem hy] at e3
    rw [e1] at h1
    have : 1 ≤ B.card := card_pos.2 ⟨y, hy⟩
    omega
  · have hne : x ≠ y := hxy.ne'
    have split : ∀ S : Finset ℚ, S ⊆ A ∪ B → ((S.filter fun z => y ≤ z).card : ℤ) =
        (S.filter fun z => x < z).card + (if x ∈ S then 1 else 0) + (if y ∈ S then 1 else 0) := by
      intro S hS
      have e : S.filter (fun z => y ≤ z) = (S.filter fun z => x < z) ∪ ((S.filter fun z => z = x) ∪ S.filter fun z => z = y) := by
        ext z
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨hzS, hyz⟩
          rcases hyz.eq_or_lt with rfl | hyz
          · exact Or.inr (Or.inr ⟨hzS, rfl⟩)
          · have : ¬ z < x := fun h' => hz z (hS hzS) ⟨hyz, h'⟩
            rcases (not_lt.1 this).eq_or_lt with rfl | h'
            · exact Or.inr (Or.inl ⟨hzS, rfl⟩)
            · exact Or.inl ⟨hzS, h'⟩
        · rintro (⟨hzS, h'⟩ | ⟨hzS, rfl⟩ | ⟨hzS, rfl⟩)
          · exact ⟨hzS, by linarith⟩
          · exact ⟨hzS, hxy.le⟩
          · exact ⟨hzS, le_rfl⟩
      have d1 : Disjoint (S.filter fun z => z = x) (S.filter fun z => z = y) :=
        disjoint_filter.2 fun z _ h1 h2 => hne (h1 ▸ h2 ▸ rfl)
      have d2 : Disjoint (S.filter fun z => x < z) ((S.filter fun z => z = x) ∪ S.filter fun z => z = y) := by
        rw [disjoint_union_right]
        exact ⟨disjoint_filter.2 fun z _ h1 h2 => by rw [h2] at h1; exact lt_irrefl _ h1,
          disjoint_filter.2 fun z _ h1 h2 => by rw [h2] at h1; linarith⟩
      rw [e, card_union_of_disjoint d2, card_union_of_disjoint d1, filter_eq' S x, filter_eq' S y]
      split_ifs <;> simp only [card_singleton, card_empty] <;> push_cast <;> ring
    have hA := split A subset_union_left
    have hB := split B subset_union_right
    have h1 : 0 ≤ ((A.filter fun z => y ≤ z).card : ℤ) - (B.filter fun z => y ≤ z).card ∧
        ((A.filter fun z => y ≤ z).card : ℤ) - (B.filter fun z => y ≤ z).card ≤ 1 := by
      have := hb _ (isUp_le y); rw [cnt_decide] at this; exact this
    have h2 : 0 ≤ ((A.filter fun z => x < z).card : ℤ) - (B.filter fun z => x < z).card ∧
        ((A.filter fun z => x < z).card : ℤ) - (B.filter fun z => x < z).card ≤ 1 := by
      have := hb _ (isUp_lt x); rw [cnt_decide] at this; exact this
    have hxAB := mem_union.1 hx
    have hyAB := mem_union.1 hy
    constructor
    · intro hxA hyA
      have hxB : x ∉ B := disjoint_left.1 hd hxA
      have hyB : y ∉ B := disjoint_left.1 hd hyA
      rw [if_pos hxA, if_pos hyA] at hA
      rw [if_neg hxB, if_neg hyB] at hB
      omega
    · intro hyA
      by_contra hxA
      have hxB : x ∈ B := hxAB.resolve_left hxA
      have hyB : y ∈ B := hyAB.resolve_left hyA
      rw [if_neg hxA, if_neg hyA] at hA
      rw [if_pos hxB, if_pos hyB] at hB
      omega

end GlobalTheory.WtInterlace

namespace GlobalTheory.WtInterlace

open Finset GlobalTheory.SignedHC

theorem good_CB (c a : ℚ) (n : ℕ) (ha : a < c - (n : ℚ) / 2) :
    Good (-1) 0 0 (TPar.block c n ∪ {a}) (TPar.block c (n + 1)) := by
  rw [block_succ_bot]
  have h := (good_blocks n c).union (good_pair ha) ?_ (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  · rwa [add_zero] at h
  · intro x hx y hy
    simp only [mem_union, mem_singleton] at hy
    have : c - (n : ℚ) / 2 < x := by
      rcases mem_union.1 hx with hx | hx
      · have := block_ge hx; linarith
      · have := block_ge hx; linarith
    rcases hy with rfl | rfl <;> linarith

theorem good_MB (e b : ℚ) (t : ℕ) (hb : e + (t : ℚ) / 2 < b) :
    Good (-1) 0 0 (TPar.block e (t + 1)) ({b} ∪ TPar.block e t) := by
  rw [block_succ_top]
  have h2 := good_blocks t (e - 1 / 2)
  rw [sub_add_cancel] at h2
  have h := (good_pair hb).union h2 ?_ (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  · rwa [add_zero] at h
  · intro x hx y hy
    simp only [mem_union, mem_singleton] at hx
    have : y ≤ e + ((t : ℚ) - 1) / 2 := by
      rcases mem_union.1 hy with hy | hy
      · have := block_le hy; linarith
      · exact block_le hy
    rcases hx with rfl | rfl <;> linarith

end GlobalTheory.WtInterlace

namespace GlobalTheory.WtInterlace

open Finset GlobalTheory.SignedHC GlobalTheory.FunObj GlobalTheory.ChiGrid

section Num

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

local notation "Γ" => num D C τ

theorem good_U {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) :
    Good (-1) 0 0 ((Γ).blockC' i ∪ {(Γ).a i}) ((Γ).blockC i) := by
  have hs : 1 ≤ (Γ).s := (odd_sLen D).pos
  have key := good_CB ((Γ).cen i : ℚ) ((Γ).a i) ((Γ).s - 1) ?_
  · rw [Nat.sub_add_cancel hs] at key
    exact key
  · have hmem : ((Γ).cen i : ℚ) - (((Γ).s - 1 : ℕ) : ℚ) / 2 ∈ (Γ).blockC i := by
      refine mem_block.2 ⟨(Γ).s - 1, by omega, ?_⟩
      rw [Nat.cast_sub hs]; push_cast; ring
    exact (blockC_bd D C τ h1 h2 hmem).1

theorem one_pow_not_mem_height_one_asIdeal {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) :
    Good (-1) 0 0 ((Γ).blockMPlus l) ({-((Γ).b l : ℚ)} ∪ (Γ).blockM l) := by
  refine good_MB (-((Γ).e l : ℚ)) (-((Γ).b l : ℚ)) (Γ).t ?_
  have := num_be D C τ h1 h2
  have e : ((Γ).t : ℚ) = D.R.t := rfl
  rw [e]; linarith

theorem lb_U {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) {x : ℚ} (hx : x ∈ ((Γ).blockC' i ∪ {(Γ).a i}) ∪ (Γ).blockC i) :
    (Γ).a i ≤ x := by
  rcases mem_union.1 hx with hx | hx
  · rcases mem_union.1 hx with hx | hx
    · exact (blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 hx).1.le
    · rw [mem_singleton.1 hx]
  · exact (blockC_bd D C τ h1 h2 hx).1.le

theorem ub_U {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) {x : ℚ} (hx : x ∈ ((Γ).blockC' i ∪ {(Γ).a i}) ∪ (Γ).blockC i) :
    x < (Γ).a i + (Γ).ga := by
  have hga : (0 : ℚ) < (Γ).ga := by
    have : 0 < (Γ).ga := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D C)
    exact_mod_cast this
  rcases mem_union.1 hx with hx | hx
  · rcases mem_union.1 hx with hx | hx
    · exact (blockC'_between (num_nearMid D C τ) (odd_sLen D).pos (sLen_lt_gap D C) h1 h2 hx).2
    · rw [mem_singleton.1 hx]; linarith
  · exact (blockC_bd D C τ h1 h2 hx).2

theorem chiGrid_row_entries_lower_bound {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) {x : ℚ} (hx : x ∈ (Γ).blockMPlus l ∪ ({-((Γ).b l : ℚ)} ∪ (Γ).blockM l)) :
    -((Γ).e l : ℚ) - (D.R.t : ℚ) / 2 ≤ x := by
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  rcases mem_union.1 hx with hx | hx
  · exact (blockMPlus_bd D C τ hx).1
  · rcases mem_union.1 hx with hx | hx
    · rw [mem_singleton.1 hx]; linarith [num_be D C τ h1 h2]
    · linarith [(blockM_bd D C τ hx).1]

theorem chiGrid_row_entries_upper_bound {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) {x : ℚ} (hx : x ∈ (Γ).blockMPlus l ∪ ({-((Γ).b l : ℚ)} ∪ (Γ).blockM l)) :
    x ≤ -((Γ).b l : ℚ) := by
  have hbe := num_be D C τ h1 h2
  rcases mem_union.1 hx with hx | hx
  · linarith [(blockMPlus_bd D C τ hx).2]
  · rcases mem_union.1 hx with hx | hx
    · rw [mem_singleton.1 hx]
    · linarith [(blockM_bd D C τ hx).2]

theorem good_top_grid : Good 0 1 1 ((Γ).weightX D.R.m) (entries ((Γ).parD D.R.m D.R.m)) := by
  have hm : (Γ).m = D.R.m := rfl
  have hk : (Γ).k = D.R.k := rfl
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have FU := good_family (fun i => (Γ).blockC' i ∪ {(Γ).a i}) (fun i => (Γ).blockC i) 1 D.R.m
    (fun i h1 h2 => good_U D C τ h1 (by omega)) fun i j h1 h2 h3 x hx y hy =>
      lt_of_lt_of_le (ub_U D C τ (by omega) (by omega) hy)
        ((a_add_le (G := Γ) h2).trans (lb_U D C τ h1 (by omega) hx))
  have FV := good_family (fun j => {(Γ).vHalf j}) (fun j => {((Γ).v j : ℚ)}) 2 (D.R.k - 1)
    (fun j _ _ => good_pair (by unfold GridData.vHalf; linarith)) fun i j h1 h2 h3 x hx y hy => by
      have hv : (Γ).v j < (Γ).v i := (Γ).v_anti i j h1 h2 (by rw [hk]; omega)
      have hv' : ((Γ).v j : ℚ) + 1 ≤ (Γ).v i := by exact_mod_cast hv
      simp only [mem_union, mem_singleton, GridData.vHalf] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
  have FW := good_family (fun l => (Γ).blockMPlus l) (fun l => {-((Γ).b l : ℚ)} ∪ (Γ).blockM l) 1 D.R.m
    (fun l h1 h2 => one_pow_not_mem_height_one_asIdeal D C τ h1 (by omega)) fun i j h1 h2 h3 x hx y hy => by
      have e1 := num_eb D C τ (l := i) h1 (by omega)
      have e2 := num_b_le D C τ (i := i + 1) (j := j) (by omega) h2 (by omega)
      have e3 := chiGrid_row_entries_lower_bound D C τ h1 (by omega) hx
      have e4 := chiGrid_row_entries_upper_bound D C τ (by omega) (by omega) hy
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      linarith
  have memU : ∀ y ∈ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC' i ∪ {(Γ).a i}) ∪
      (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC i), ∃ i, 1 ≤ i ∧ i ≤ D.R.m ∧
        y ∈ ((Γ).blockC' i ∪ {(Γ).a i}) ∪ (Γ).blockC i := by
    intro y hy
    rw [← biUnion_union] at hy
    obtain ⟨i, hi, hy⟩ := mem_biUnion.1 hy
    rw [mem_Ico] at hi
    exact ⟨i, hi.1, by omega, hy⟩
  have memV : ∀ y ∈ (Ico 2 (2 + (D.R.k - 1))).biUnion (fun j => ({(Γ).vHalf j} : Finset ℚ)) ∪
      (Ico 2 (2 + (D.R.k - 1))).biUnion (fun j => ({((Γ).v j : ℚ)} : Finset ℚ)), ∃ j, 2 ≤ j ∧ j ≤ D.R.k ∧
        (y = (Γ).vHalf j ∨ y = (Γ).v j) := by
    intro y hy
    rw [← biUnion_union] at hy
    obtain ⟨j, hj, hy⟩ := mem_biUnion.1 hy
    rw [mem_Ico] at hj
    simp only [mem_union, mem_singleton] at hy
    exact ⟨j, hj.1, by omega, hy⟩
  have memW : ∀ y ∈ (Ico 1 (1 + D.R.m)).biUnion (fun l => (Γ).blockMPlus l) ∪
      (Ico 1 (1 + D.R.m)).biUnion (fun l => {-((Γ).b l : ℚ)} ∪ (Γ).blockM l), ∃ l, 1 ≤ l ∧ l ≤ D.R.m ∧
        y ∈ (Γ).blockMPlus l ∪ ({-((Γ).b l : ℚ)} ∪ (Γ).blockM l) := by
    intro y hy
    rw [← biUnion_union] at hy
    obtain ⟨l, hl, hy⟩ := mem_biUnion.1 hy
    rw [mem_Ico] at hl
    exact ⟨l, hl.1, by omega, hy⟩
  have T1 := (good_single ((Γ).a 0)).union FU (fun x hx y hy => by
      obtain ⟨i, h1, h2, hy⟩ := memU y hy
      have hx' : x = (Γ).a 0 := by simpa using hx
      rw [hx']
      exact lt_of_lt_of_le (ub_U D C τ h1 h2 hy) (a_add_le (G := Γ) (by omega)))
    (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  have lb1 : ∀ x ∈ ({(Γ).a 0} ∪ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC' i ∪ {(Γ).a i})) ∪
      (∅ ∪ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC i)), (Γ).a (Γ).m ≤ x := by
    intro x hx
    simp only [empty_union] at hx
    rcases mem_union.1 hx with hx | hx
    · rcases mem_union.1 hx with hx | hx
      · rw [mem_singleton.1 hx]; exact a_le D C τ (Nat.zero_le _)
      · obtain ⟨i, h1, h2, hx⟩ := memU x (mem_union_left _ hx)
        exact (a_le D C τ (by rw [hm]; exact h2)).trans (lb_U D C τ h1 h2 hx)
    · obtain ⟨i, h1, h2, hx⟩ := memU x (mem_union_right _ hx)
      exact (a_le D C τ (by rw [hm]; exact h2)).trans (lb_U D C τ h1 h2 hx)
  have T2 := T1.union FV (fun x hx y hy => by
      obtain ⟨j, h1, h2, hy⟩ := memV y hy
      have := v_lt_a D C τ h1 h2
      have := lb1 x hx
      rcases hy with rfl | rfl
      · unfold GridData.vHalf; linarith
      · linarith)
    (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  have hb1 : -((Γ).b 1 : ℚ) < (Γ).a (Γ).m := low_lt_a D C τ le_rfl
  have T3 := T2.union FW (fun x hx y hy => by
      obtain ⟨l, h1, h2, hy⟩ := memW y hy
      have e1 := chiGrid_row_entries_upper_bound D C τ h1 h2 hy
      have e2 := num_b_le D C τ (i := 1) (j := l) le_rfl h1 h2
      have lx : -((Γ).b 1 : ℚ) < x := by
        rcases mem_union.1 hx with hx | hx
        · rcases mem_union.1 hx with hx | hx
          · linarith [lb1 x (mem_union_left _ hx)]
          · obtain ⟨j, h1, h2, hx⟩ := memV x (mem_union_left _ hx)
            have := num_cloud D C τ h1 h2
            rcases hx with rfl | rfl
            · unfold GridData.vHalf; linarith
            · linarith
        · rcases mem_union.1 hx with hx | hx
          · linarith [lb1 x (mem_union_right _ hx)]
          · obtain ⟨j, h1, h2, hx⟩ := memV x (mem_union_right _ hx)
            have := num_cloud D C τ h1 h2
            rcases hx with rfl | rfl
            · unfold GridData.vHalf; linarith
            · linarith
      linarith)
    (le_refl _) (le_refl _) (by norm_num) (by norm_num)
  have hA : {(Γ).a 0} ∪ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC' i ∪ {(Γ).a i}) ∪
      (Ico 2 (2 + (D.R.k - 1))).biUnion (fun j => ({(Γ).vHalf j} : Finset ℚ)) ∪
      (Ico 1 (1 + D.R.m)).biUnion (fun l => (Γ).blockMPlus l) = (Γ).weightX D.R.m := by
    ext x
    simp only [mem_union, mem_singleton, mem_biUnion, mem_Ico, GridData.mem_weightX, GridData.mem_tops,
      GridData.mem_cloudHalf, hm, hk]
    constructor
    · rintro (((hx | ⟨i, ⟨h1, h2⟩, hx | hx⟩) | ⟨j, ⟨h1, h2⟩, hx⟩) | ⟨l, ⟨h1, h2⟩, hx⟩)
      · exact Or.inl ⟨0, Nat.zero_le _, hx⟩
      · exact Or.inr (Or.inr (Or.inl ⟨i, h1, by omega, hx⟩))
      · exact Or.inl ⟨i, by omega, hx⟩
      · exact Or.inr (Or.inl ⟨j, h1, by omega, hx⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨l, h1, by omega, hx⟩))
    · rintro (⟨i, hi, hx⟩ | ⟨j, h1, h2, hx⟩ | ⟨i, h1, h2, hx⟩ | ⟨l, h1, h2, hx⟩)
      · rcases Nat.eq_zero_or_pos i with rfl | h
        · exact Or.inl (Or.inl (Or.inl hx))
        · exact Or.inl (Or.inl (Or.inr ⟨i, ⟨h, by omega⟩, Or.inr hx⟩))
      · exact Or.inl (Or.inr ⟨j, ⟨h1, by omega⟩, hx⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨i, ⟨h1, by omega⟩, Or.inl hx⟩))
      · exact Or.inr ⟨l, ⟨h1, by omega⟩, hx⟩
  have hB : ∅ ∪ (Ico 1 (1 + D.R.m)).biUnion (fun i => (Γ).blockC i) ∪
      (Ico 2 (2 + (D.R.k - 1))).biUnion (fun j => ({((Γ).v j : ℚ)} : Finset ℚ)) ∪
      (Ico 1 (1 + D.R.m)).biUnion (fun l => {-((Γ).b l : ℚ)} ∪ (Γ).blockM l) = entries ((Γ).parD D.R.m D.R.m) := by
    ext x
    rw [GridData.entries_parD]
    simp only [empty_union, mem_union, mem_singleton, mem_biUnion, mem_Ico, mem_Icc, GridData.mem_cloud,
      GridData.mem_lows, hm, hk]
    constructor
    · rintro ((⟨i, ⟨h1, h2⟩, hx⟩ | ⟨j, ⟨h1, h2⟩, hx⟩) | ⟨l, ⟨h1, h2⟩, hx | hx⟩)
      · exact Or.inr ⟨i, ⟨by omega, by omega⟩, hx⟩
      · exact Or.inl (Or.inl (Or.inl ⟨j, h1, by omega, hx⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨l, h1, by omega, hx⟩))
      · exact Or.inl (Or.inr ⟨l, ⟨h1, by omega⟩, hx⟩)
    · rintro (((⟨j, h1, h2, hx⟩ | ⟨l, h1, h2, hx⟩) | ⟨l, ⟨h1, h2⟩, hx⟩) | ⟨i, ⟨h1, h2⟩, hx⟩)
      · exact Or.inl (Or.inr ⟨j, ⟨h1, by omega⟩, hx⟩)
      · exact Or.inr ⟨l, ⟨h1, by omega⟩, Or.inl hx⟩
      · exact Or.inr ⟨l, ⟨h1, by omega⟩, Or.inr hx⟩
      · exact Or.inl (Or.inl ⟨i, ⟨by omega, by omega⟩, hx⟩)
  exact good_congr T3 hA hB

end Num

end GlobalTheory.WtInterlace

namespace GlobalTheory.WtInterlace

open Finset GlobalTheory.SignedHC GlobalTheory.FunObj GlobalTheory.ChiGrid

theorem interlace_wtOf {N n : ℕ} (hN : N = n + 1) {A B : Finset ℚ} (hA : A.card = N) (hB : B.card = n)
    (hAc : InCoset (((N : ℚ) - 1) / 2) A) (hBc : InCoset (((n : ℚ) - 1) / 2) B) (hSI : StrictInterlace A B) :
    Formalism.L2.Col.Br.Interlace hN (wtOf N A) (wtOf n B) := by
  subst hN
  have key := (strictInterlace_iff_descEnum hA hB).1 hSI
  intro i
  have eA : ∀ j, ((wtOf (n + 1) A).w j : ℚ) = descEnum A hA j - ((((n + 1 : ℕ) : ℚ) - 1) / 2 - ((j : ℕ) : ℚ)) :=
    fun j => wtOf_cast hA hAc j
  have eB : ∀ j, ((wtOf n B).w j : ℚ) = descEnum B hB j - (((n : ℚ) - 1) / 2 - ((j : ℕ) : ℚ)) :=
    fun j => wtOf_cast hB hBc j
  have s1 : Formalism.L2.Col.Br.iS (rfl : n + 1 = n + 1) i = i.succ := Fin.ext rfl
  have s2 : Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) i = i.castSucc := Fin.ext rfl
  have h1 := eA i.succ
  have h2 := eA i.castSucc
  have h3 := eB i
  obtain ⟨k1, k2⟩ := key i
  simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
  push_cast at h1 h2
  unfold Formalism.L2.Col.Br.aBr Formalism.L2.Col.Br.bBr
  rw [s1, s2]
  constructor
  · have : (-1 : ℚ) < (((wtOf n B).w i - (wtOf (n + 1) A).w i.succ : ℤ) : ℚ) := by
      push_cast; rw [h1, h3]; linarith
    have : (-1 : ℤ) < (wtOf n B).w i - (wtOf (n + 1) A).w i.succ := by exact_mod_cast this
    omega
  · have : (-1 : ℚ) < (((wtOf (n + 1) A).w i.castSucc - (wtOf n B).w i : ℤ) : ℚ) := by
      push_cast; rw [h2, h3]; linarith
    have : (-1 : ℤ) < (wtOf (n + 1) A).w i.castSucc - (wtOf n B).w i := by exact_mod_cast this
    omega

theorem descEnum_last {m : ℕ} {E : Finset ℚ} (h : E.card = m) (hm : 0 < m) {z : ℚ} (hz : z ∈ E)
    (hmin : ∀ y ∈ E, z ≤ y) : descEnum E h ⟨m - 1, by omega⟩ = z := by
  apply le_antisymm
  · rw [← image_descEnum E h] at hz
    obtain ⟨j, -, hj⟩ := mem_image.1 hz
    rw [← hj]
    exact (strictAnti_descEnum E h).antitone (Fin.mk_le_mk.2 (by have := j.2; omega))
  · exact hmin _ (descEnum_mem E h _)

theorem sameShift_wtOf {N n : ℕ} (hN : N = n + 1) (hn : 0 < n) {A B : Finset ℚ} (hA : A.card = N) (hB : B.card = n)
    (hAc : InCoset (((N : ℚ) - 1) / 2) A) (hBc : InCoset (((n : ℚ) - 1) / 2) B) {x : ℚ} (hxA : x ∈ A)
    (hAm : ∀ y ∈ A, x ≤ y) (hxB : x + 1 / 2 ∈ B) (hBm : ∀ y ∈ B, x + 1 / 2 ≤ y) :
    Formalism.L2.Col.Br.SameShift (wtOf N A) (wtOf n B) := by
  subst hN
  unfold Formalism.L2.Col.Br.SameShift DomWeight.detShift
  rw [dif_pos hn, dif_pos (Nat.succ_pos n)]
  have e1 := wtOf_cast hB hBc ⟨n - 1, by omega⟩
  have e2 := wtOf_cast hA hAc ⟨n + 1 - 1, by omega⟩
  simp only [highestWeight] at e1 e2
  rw [descEnum_last hB hn hxB hBm] at e1
  rw [descEnum_last hA (Nat.succ_pos n) hxA hAm] at e2
  have : (((wtOf n B).w ⟨n - 1, by omega⟩ : ℤ) : ℚ) = (((wtOf (n + 1) A).w ⟨n + 1 - 1, by omega⟩ : ℤ) : ℚ) := by
    rw [e1, e2]
    rw [Nat.cast_sub hn]
    push_cast
    ring
  exact_mod_cast this

end GlobalTheory.WtInterlace

namespace GlobalTheory.WtInterlace

open Finset GlobalTheory.SignedHC GlobalTheory.FunObj GlobalTheory.ChiGrid

section Min

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

local notation "Γ" => num D C τ

theorem low_mem_weightX : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 ∈ (Γ).weightX D.R.m := by
  have hm2 := D.R.two_le_m
  have et : ((Γ).t : ℚ) = D.R.t := rfl
  refine GridData.mem_weightX.2 (Or.inr (Or.inr (Or.inr ⟨D.R.m, by omega, le_rfl, mem_block.2 ⟨(Γ).t, by omega, ?_⟩⟩)))
  push_cast
  rw [et]
  ring

theorem min_weightX {y : ℚ} (hy : y ∈ (Γ).weightX D.R.m) : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 ≤ y := by
  have hm2 := D.R.two_le_m
  have hz := low_mem_weightX D C τ
  obtain ⟨j, hj⟩ : ∃ j, D.R.m = j + 1 := ⟨D.R.m - 1, by omega⟩
  have hz' : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 ∈ (Γ).blockMPlus D.R.m := by
    have et : ((Γ).t : ℚ) = D.R.t := rfl
    refine mem_block.2 ⟨(Γ).t, by omega, ?_⟩
    push_cast
    rw [et]
    ring
  rw [hj] at hy hz' ⊢
  rw [GridData.weightX_succ] at hy
  rcases mem_union.1 hy with hy | hy
  · exact (weightX_above D C τ (j := j) (by omega) hy hz').le
  · exact (blockMPlus_bd D C τ hy).1

theorem half_mem_parD : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 + 1 / 2 ∈ entries ((Γ).parD D.R.m D.R.m) := by
  have hm2 := D.R.two_le_m
  have ht := D.R.t_odd.pos
  have et : ((Γ).t : ℚ) = D.R.t := rfl
  have hmem : -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 + 1 / 2 ∈ (Γ).blockM D.R.m := by
    refine mem_block.2 ⟨(Γ).t - 1, by show D.R.t - 1 < D.R.t; omega, ?_⟩
    rw [Nat.cast_sub (show 1 ≤ (Γ).t from ht), et]
    ring
  rw [GridData.entries_parD]
  exact mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨D.R.m, mem_Icc.2 ⟨by omega, le_rfl⟩, hmem⟩))

theorem min_parD {y : ℚ} (hy : y ∈ entries ((Γ).parD D.R.m D.R.m)) :
    -((Γ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2 + 1 / 2 ≤ y := by
  have hm2 := D.R.two_le_m
  have hm : (Γ).m = D.R.m := rfl
  have hbe := num_be D C τ (l := D.R.m) (by omega) le_rfl
  have hbm := num_b_le D C τ (i := 1) (j := D.R.m) le_rfl (by omega) le_rfl
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  rw [GridData.entries_parD] at hy
  rcases mem_union.1 hy with hy | hy
  · rcases mem_union.1 hy with hy | hy
    · rcases mem_union.1 hy with hy | hy
      · have := (cloud_gt D C τ hy).1
        linarith
      · obtain ⟨l, h1, h2, rfl⟩ := GridData.mem_lows.1 hy
        have := num_b_le D C τ (i := l) (j := D.R.m) h1 (by rw [← hm]; exact h2) le_rfl
        linarith
    · obtain ⟨l, hl, hy⟩ := mem_biUnion.1 hy
      simp only [mem_Icc, hm] at hl
      have e1 := (blockM_bd D C τ hy).1
      have e2 : ((Γ).e l : ℚ) ≤ (Γ).e D.R.m := by
        rcases hl.2.eq_or_lt with h | h
        · rw [h]
        · linarith [num_e_lt D C τ hl.1 h le_rfl]
      linarith
  · obtain ⟨l, hl, hy⟩ := mem_biUnion.1 hy
    simp only [mem_Icc, hm] at hl
    have e1 := (blockC_bd D C τ (by omega) hl.2 hy).1
    have e2 := a_le D C τ (i := l) (j := (Γ).m) (by rw [hm]; exact hl.2)
    have e3 : -((Γ).b 1 : ℚ) < (Γ).a (Γ).m := low_lt_a D C τ le_rfl
    linarith

end Min

theorem weights_top_grid : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (τ : D.what₂.Tau),
    Formalism.L2.Col.Br.Interlace G.sp.topDec.rank.symm (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) ∧
      Formalism.L2.Col.Br.SameShift (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) := by
  intro D T L sc G τ
  have r0 := rank_top G (j := D.R.m) le_rfl
  have r1 := rank_grid G (i := D.R.m) le_rfl
  have h0 := isHC_top D sc.cGap τ (j := D.R.m) le_rfl r0
  have h1 := isHC_grid D sc.cGap τ (i := D.R.m) le_rfl r1
  have hA := h0.1.card_entries.trans h0.2.1
  have hB := h1.1.card_entries.trans h1.2.1
  have eA : entries (Node.par D sc.cGap (.top D.R.m) τ) = (num D sc.cGap τ).weightX D.R.m := entries_plus _
  have eB : entries (Node.par D sc.cGap (.grid D.R.m D.R.m) τ) = entries ((num D sc.cGap τ).parD D.R.m D.R.m) := by
    have : entries (Node.par D sc.cGap (.grid D.R.m D.R.m) τ) =
        entries (shift (if Odd (D.R.m + D.R.m) then -(1 / 2) else 0) ((num D sc.cGap τ).parD D.R.m (num D sc.cGap τ).m)) := rfl
    rw [this, if_neg (by rw [Nat.odd_iff]; omega), shift_zero]
    rfl
  have hSI : StrictInterlace (entries (Node.par D sc.cGap (.top D.R.m) τ))
      (entries (Node.par D sc.cGap (.grid D.R.m D.R.m) τ)) := by
    rw [eA, eB]; exact strictInterlace_of_good (good_top_grid D sc.cGap τ)
  have hn : 0 < (G.V (.grid D.R.m D.R.m)).rank := by rw [r1]; exact rankV_pos D _ _
  refine ⟨interlace_wtOf G.sp.topDec.rank.symm hA hB h0.2.2 h1.2.2 hSI,
    sameShift_wtOf G.sp.topDec.rank.symm hn hA hB h0.2.2 h1.2.2
      (x := -((num D sc.cGap τ).e D.R.m : ℚ) - (D.R.t : ℚ) / 2) ?_ ?_ ?_ ?_⟩
  · rw [eA]; exact low_mem_weightX D sc.cGap τ
  · rw [eA]; exact fun y hy => min_weightX D sc.cGap τ hy
  · rw [eB]; exact half_mem_parD D sc.cGap τ
  · rw [eB]; exact fun y hy => min_parD D sc.cGap τ hy

end GlobalTheory.WtInterlace
