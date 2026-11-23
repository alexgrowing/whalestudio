import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilSignShift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig shiftPar alV alW lamS lamT StepGap StepWeil VacVec fockOf)

namespace GlobalTheory.Chain.ItPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_signed {l₁ l₂ : List ℚ} {c x : ℚ} {s : Bool} :
    (x, s) ∈ signed l₁ l₂ c ↔ (s = true ∧ x - c ∈ l₁) ∨ (s = false ∧ x - c ∈ l₂) := by
  simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨a, ha, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, by simpa using ha⟩
    · exact Or.inr ⟨rfl, by simpa using ha⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact Or.inl ⟨_, h, by ring, rfl⟩
    · exact Or.inr ⟨_, h, by ring, rfl⟩

theorem mem_shiftPar {S : SPar} {c x : ℚ} {s : Bool} : (x, s) ∈ shiftPar c S ↔ (x - c, s) ∈ S := by
  simp only [shiftPar, Finset.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, h, rfl, rfl⟩; simpa using h
  · intro h; exact ⟨_, _, h, by ring, rfl⟩

theorem eq_signed_iff {S : SPar} {l₁ l₂ : List ℚ} {c : ℚ} :
    S = signed l₁ l₂ c ↔ shiftPar (-c) S = signed l₁ l₂ 0 := by
  constructor
  · rintro rfl
    ext ⟨x, s⟩
    simp [mem_shiftPar, mem_signed]
  · intro h
    ext ⟨x, s⟩
    have := congrArg (fun U => (x - c, s) ∈ U) h
    simpa [mem_shiftPar, mem_signed] using this

theorem mem_iff_getD {l : List ℚ} {n : ℕ} (hn : n = l.length) {x : ℚ} : x ∈ l ↔ ∃ i : Fin n, l.getD i 0 = x := by
  subst hn
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, List.getD_eq_getElem _ _ hi⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, (List.getD_eq_getElem _ _ i.2).symm⟩

theorem cross_iff {p q : ℕ} {l₁ l₂ : List ℚ} (hp : p = l₁.length) (hq : q = l₂.length) (P : ℚ → Prop) :
    (∀ a b : Formalism.BasicNotions.TH.Ix p q, ¬ sameBlock a b → P (ofBlocks l₁ l₂ a - ofBlocks l₁ l₂ b)) ↔
      ∀ x ∈ signed l₁ l₂ 0, ∀ y ∈ signed l₁ l₂ 0, x.2 ≠ y.2 → P (x.1 - y.1) := by
  constructor
  · rintro h ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    simp only [mem_signed, sub_zero] at hx hy
    rcases hx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;> rcases hy with ⟨rfl, hy⟩ | ⟨rfl, hy⟩
    · exact absurd rfl hs
    · obtain ⟨i, rfl⟩ := (mem_iff_getD hp).1 hx
      obtain ⟨j, rfl⟩ := (mem_iff_getD hq).1 hy
      exact h (.inl i) (.inr j) (fun h => h)
    · obtain ⟨i, rfl⟩ := (mem_iff_getD hq).1 hx
      obtain ⟨j, rfl⟩ := (mem_iff_getD hp).1 hy
      exact h (.inr i) (.inl j) (fun h => h)
    · exact absurd rfl hs
  · intro h a b hab
    have h1 : ∀ i : Fin p, (l₁.getD i 0, true) ∈ signed l₁ l₂ 0 := fun i =>
      mem_signed.2 (Or.inl ⟨rfl, by rw [sub_zero]; exact (mem_iff_getD hp).2 ⟨i, rfl⟩⟩)
    have h2 : ∀ i : Fin q, (l₂.getD i 0, false) ∈ signed l₁ l₂ 0 := fun i =>
      mem_signed.2 (Or.inr ⟨rfl, by rw [sub_zero]; exact (mem_iff_getD hq).2 ⟨i, rfl⟩⟩)
    rcases a with i | i <;> rcases b with j | j
    · exact absurd trivial hab
    · exact h _ (h1 i) _ (h2 j) (by simp)
    · exact h _ (h2 i) _ (h1 j) (by simp)
    · exact absurd trivial hab

theorem card_filter_true {l₁ l₂ : List ℚ} (h : l₁.Nodup) :
    ((signed l₁ l₂ 0).filter fun x => x.2 = true).card = l₁.length := by
  have : ((signed l₁ l₂ 0).filter fun x => x.2 = true) = l₁.toFinset.image fun x => (x, true) := by
    ext ⟨x, s⟩
    cases s <;> simp [mem_signed]
  rw [this, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), List.toFinset_card_of_nodup h]

theorem card_filter_false {l₁ l₂ : List ℚ} (h : l₂.Nodup) :
    ((signed l₁ l₂ 0).filter fun x => x.2 = false).card = l₂.length := by
  have : ((signed l₁ l₂ 0).filter fun x => x.2 = false) = l₂.toFinset.image fun x => (x, false) := by
    ext ⟨x, s⟩
    cases s <;> simp [mem_signed]
  rw [this, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), List.toFinset_card_of_nodup h]

theorem card_signed {l₁ l₂ : List ℚ} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) :
    (signed l₁ l₂ 0).card = l₁.length + l₂.length := by
  rw [← card_filter_true (l₂ := l₂) h₁, ← card_filter_false (l₁ := l₁) h₂,
    ← Finset.card_filter_add_card_filter_not (s := signed l₁ l₂ 0) (fun x => x.2 = true)]
  simp

theorem hypG_iff {t n : ℕ} {al be ga de : List ℚ} (hnd : (al ++ be ++ ga ++ de).Nodup)
    (hn : (signed (al ++ be) (ga ++ de) 0).card = n) :
    HypG t al be ga de ↔
      NcGapGt (signed (al ++ be) (ga ++ de) 0) (((n + t : ℕ) : ℝ) ^ 3) ∧
      NcGapGt (signed (al ++ block t ++ de) (ga ++ be) 0) (((n + t : ℕ) : ℝ) ^ 3) ∧
      NcGapGe (signed (al ++ be) (ga ++ de) 0)
        (120 * (n : ℝ) * (minSig (signed (al ++ be) (ga ++ de) 0) : ℝ) ^ ((3 : ℝ) / 2)) := by
  rw [List.append_assoc (al ++ be)] at hnd
  have h₁ := hnd.of_append_left
  have h₂ := hnd.of_append_right
  have hn' : al.length + be.length + ga.length + de.length = n := by
    rw [← hn, card_signed h₁ h₂]; simp only [List.length_append]; omega
  have hm : minSig (signed (al ++ be) (ga ++ de) 0) = min (al.length + be.length) (ga.length + de.length) := by
    rw [minSig, card_filter_true h₁, card_filter_false h₂, List.length_append, List.length_append]
  have hb : (block t).length = t := by simp [block]
  rw [hm, HypG, hn']
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact cross_iff (by simp) (by simp) fun z => ((n + t : ℕ) : ℝ) ^ 3 < |(z : ℝ)|
  · exact cross_iff (by simp [hb]; omega) (by simp) fun z => ((n + t : ℕ) : ℝ) ^ 3 < |(z : ℝ)|
  · exact cross_iff (by simp) (by simp) fun z => 120 * (n : ℝ) *
      ((min (al.length + be.length) (ga.length + de.length) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ |(z : ℝ)|

theorem exists_desc (A : Finset ℚ) : ∃ l : List ℚ, l.Pairwise (· > ·) ∧ ∀ x, x ∈ l ↔ x ∈ A := by
  refine ⟨A.sort (· ≥ ·), ?_, fun x => Finset.mem_sort _⟩
  exact ((A.pairwise_sort (· ≥ ·)).and (A.sort_nodup (· ≥ ·))).imp fun h => lt_of_le_of_ne h.1 (Ne.symm h.2)

theorem exists_lists {t : ℕ} (ht : 1 ≤ t) {S S' : SPar} (hne : S.Nonempty)
    (inj : ∀ x, (x, true) ∈ S → (x, false) ∉ S)
    (big : ∀ x s, (x, s) ∈ S → ((t : ℚ) + 3) / 2 ≤ |x|)
    (int : ∀ x s, (x, s) ∈ S → ∃ z : ℤ, x = ((t : ℚ) + 1) / 2 + z)
    (hS' : ∀ x s, (x, s) ∈ S' ↔ (x ∈ block t ∧ s = true) ∨ (0 < x ∧ (x, s) ∈ S) ∨ (x < 0 ∧ (x, !s) ∈ S)) :
    ∃ al be ga de : List ℚ, HypA t al be ga de ∧ (∀ e ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |e|) ∧
      S = signed (al ++ be) (ga ++ de) 0 ∧ S' = signed (al ++ block t ++ de) (ga ++ be) 0 := by
  have key : ∀ (s : Bool) (p : ℚ → Prop), ∃ l : List ℚ, l.Pairwise (· > ·) ∧ ∀ x, x ∈ l ↔ p x ∧ (x, s) ∈ S := by
    intro s p
    classical
    obtain ⟨l, h1, h2⟩ := exists_desc (((S.filter fun y => y.2 = s).image Prod.fst).filter p)
    refine ⟨l, h1, fun x => ?_⟩
    rw [h2]; simp [and_comm]
  obtain ⟨al, pa, ha⟩ := key true (0 < ·)
  obtain ⟨be, pb, hb⟩ := key true (· < 0)
  obtain ⟨ga, pg, hg⟩ := key false (0 < ·)
  obtain ⟨de, pd, hd⟩ := key false (· < 0)
  have ht0 : (0 : ℚ) ≤ t := by positivity
  have nz : ∀ x s, (x, s) ∈ S → 0 < x ∨ x < 0 := by
    intro x s h
    have := big x s h
    rcases lt_trichotomy x 0 with h | rfl | h
    · exact Or.inr h
    · rw [abs_zero] at this; linarith
    · exact Or.inl h
  have all : ∀ e ∈ al ++ be ++ ga ++ de, ∃ s, (e, s) ∈ S := by
    intro e he
    simp only [List.mem_append, ha, hb, hg, hd] at he
    rcases he with ((h | h) | h) | h <;> exact ⟨_, h.2⟩
  have hS : S = signed (al ++ be) (ga ++ de) 0 := by
    ext ⟨x, s⟩
    have := nz x s
    cases s <;> simp [mem_signed, ha, hb, hg, hd] <;> tauto
  have nd : ∀ {l : List ℚ}, l.Pairwise (· > ·) → l.Nodup := fun h => h.imp fun h => h.ne'
  refine ⟨al, be, ga, de, ⟨ht, ?_, pa, pb, pg, pd, ?_, ?_, ?_, ?_, ?_⟩, ?_, hS, ?_⟩
  · obtain ⟨⟨x, s⟩, hx⟩ := hne
    rw [hS, mem_signed] at hx
    rcases hx with ⟨-, hx⟩ | ⟨-, hx⟩ <;>
    · have := List.length_pos_of_mem hx
      rw [List.length_append] at this; omega
  · simp only [List.nodup_append, nd pa, nd pb, nd pg, nd pd, List.mem_append, ha, hb, hg, hd, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro a h1 b h2 rfl; exact lt_asymm h1.1 h2.1
    · rintro a (h1 | h1) b h2 rfl <;> exact inj _ h1.2 h2.2
    · rintro a ((h1 | h1) | h1) b h2 rfl
      · exact inj _ h1.2 h2.2
      · exact inj _ h1.2 h2.2
      · exact lt_asymm h1.1 h2.1
  · intro e he
    simp only [List.mem_append, ha, hg] at he
    rcases he with h | h <;> exact h.1
  · intro e he
    simp only [List.mem_append, hb, hd] at he
    rcases he with h | h <;> exact h.1
  · intro e he; obtain ⟨s, h⟩ := all e he; exact int e s h
  · intro e he; obtain ⟨s, h⟩ := all e he; have := big e s h; linarith
  · intro e he; obtain ⟨s, h⟩ := all e he; exact big e s h
  · ext ⟨x, s⟩
    rw [hS']
    cases s <;> simp [mem_signed, ha, hb, hg, hd] <;> tauto

section HC

variable {R : Ranks} (P : HCParam R)

theorem gap_of_lt {i j : Fin R.m} (h : i.1 < j.1) : ((R.t : ℚ) + 3) / 2 ≤ P.b j - P.e i := by
  have key : ∀ (n : ℕ) (h : i.1 + n + 1 < R.m), ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨i.1 + n + 1, h⟩ - P.e i := by
    intro n
    induction n with
    | zero => intro h; exact P.gap_eb i h
    | succ n ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := P.gap_be ⟨i.1 + n + 1, by omega⟩
      have h3 := P.gap_eb ⟨i.1 + n + 1, by omega⟩ h
      have ht : (0 : ℚ) ≤ R.t := by positivity
      have e : P.b ⟨i.1 + (n + 1) + 1, h⟩ = P.b ⟨i.1 + n + 1 + 1, h⟩ := rfl
      rw [e]; linarith
  obtain ⟨j, hj⟩ := j
  obtain ⟨n, rfl⟩ : ∃ n, j = i.1 + n + 1 := ⟨j - i.1 - 1, by simp at h; omega⟩
  exact key n hj

theorem gap_of_le {i j : Fin R.m} (h : i.1 ≤ j.1) : ((R.t : ℚ) + 3) / 2 ≤ P.e j - P.b i := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  rcases h.eq_or_lt with h | h
  · rw [Fin.ext h]; exact P.gap_be j
  · have := gap_of_lt P h; have := P.gap_be i; have := P.gap_be j; linarith

theorem v_anti : StrictAnti P.v := by
  have hs : ∀ (a : ℕ) (h : a + 1 < R.k - 1), P.v ⟨a + 1, h⟩ < P.v ⟨a, by omega⟩ :=
    fun a h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩)
  have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.k - 1), P.v ⟨a + d + 1, h⟩ < P.v ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => exact hs
    | succ d ih => intro a h; exact (hs (a + d + 1) h).trans (ih a (by omega))
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < b from hab)
  exact hA d a hb

theorem neg_b_lt_v (i : Fin (R.k - 1)) (j : Fin R.m) : -P.b j < P.v i := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 := P.u_last_gt (by omega) (by omega)
  have h2 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have e : P.u ⟨R.k - 2 + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ := by congr 2; omega
  have h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i := (v_anti P).antitone (show i.1 ≤ R.k - 2 by have := i.2; omega)
  have h4 : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rcases Nat.eq_zero_or_pos j.1 with h | h
    · exact le_of_eq (congrArg P.b (Fin.ext h.symm))
    · have := gap_of_lt P (i := ⟨0, by omega⟩) (j := j) h
      have := P.gap_be ⟨0, by omega⟩
      have ht : (0 : ℚ) ≤ R.t := by positivity
      linarith
  simp only at h2
  rw [e] at h2
  linarith

abbrev Idx (R : Ranks) (j : ℕ) : Type := Fin (R.k - 1) ⊕ Fin R.m ⊕ ({i : Fin R.m // (i : ℕ) < j} × Fin R.t)

def val (j : ℕ) : Idx R j → ℚ
  | .inl i => P.v i
  | .inr (.inl i) => -P.b i
  | .inr (.inr x) => -P.e x.1.1 + ((R.t : ℚ) - 1) / 2 - (x.2.1 : ℚ)

def sgn (R : Ranks) (j : ℕ) : Idx R j → Bool
  | .inl _ => true
  | .inr (.inl i) => decide (i.1 ≤ j ∨ Even (i.1 - j))
  | .inr (.inr _) => true

theorem card_idx {j : ℕ} (hj : j ≤ R.m) : Fintype.card (Idx R j) = R.rankY j := by
  have hk := R.m_add_three_le_k
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin_lt_of_le hj, Ranks.rankY, Ranks.r]
  omega

theorem cast_bounds (a : Fin R.t) : (0 : ℚ) ≤ (a.1 : ℚ) ∧ (a.1 : ℚ) + 1 ≤ R.t :=
  ⟨by positivity, by exact_mod_cast a.2⟩

theorem val_injective (j : ℕ) : Function.Injective (val P j) := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have vb := neg_b_lt_v P
  have ve : ∀ i (l : Fin R.m) (a : Fin R.t), P.v i ≠ -P.e l + ((R.t : ℚ) - 1) / 2 - (a.1 : ℚ) := by
    intro i l a h
    have := vb i l; have := P.gap_be l; have := cast_bounds a; linarith
  have be : ∀ (i l : Fin R.m) (a : Fin R.t), -P.b i ≠ -P.e l + ((R.t : ℚ) - 1) / 2 - (a.1 : ℚ) := by
    intro i l a h
    have := cast_bounds a
    rcases le_or_gt i.1 l.1 with h' | h'
    · have := gap_of_le P h'; linarith
    · have := gap_of_lt P h'; linarith
  rintro (i | i | ⟨⟨i, hi⟩, a⟩) (l | l | ⟨⟨l, hl⟩, b⟩) h <;> simp only [val] at h
  · rw [(v_anti P).injective h]
  · exact absurd h (vb i l).ne'
  · exact absurd h (ve _ _ _)
  · exact absurd h (vb l i).ne
  · rcases lt_trichotomy i.1 l.1 with h' | h' | h'
    · have := gap_of_lt P h'; have := P.gap_be i; linarith
    · rw [Fin.ext h']
    · have := gap_of_lt P h'; have := P.gap_be l; linarith
  · exact absurd h (be _ _ _)
  · exact absurd h.symm (ve _ _ _)
  · exact absurd h.symm (be _ _ _)
  · have := cast_bounds a
    have := cast_bounds b
    rcases lt_trichotomy i.1 l.1 with h' | h' | h'
    · have := gap_of_lt P h'; have := P.gap_be l; linarith
    · obtain rfl := Fin.ext h'
      have h1 : (a.1 : ℚ) = b.1 := by linarith
      rw [Fin.ext (show a.1 = b.1 by exact_mod_cast h1)]
    · have := gap_of_lt P h'; have := P.gap_be i; linarith

theorem val_big (k : Fin R.m) (x : Idx R k) : ((R.t : ℚ) + 3) / 2 ≤ |val P k x + P.e k| := by
  rcases x with i | i | ⟨⟨i, hi⟩, a⟩ <;> simp only [val]
  · have := neg_b_lt_v P i k; have := P.gap_be k
    exact le_abs.2 (Or.inl (by linarith))
  · rcases le_or_gt i.1 k.1 with h | h
    · have := gap_of_le P h; exact le_abs.2 (Or.inl (by linarith))
    · have := gap_of_lt P h; exact le_abs.2 (Or.inr (by linarith))
  · have := gap_of_lt P hi; have := P.gap_be k; have := cast_bounds a
    exact le_abs.2 (Or.inl (by linarith))

theorem val_int (k : Fin R.m) (x : Idx R k) : ∃ z : ℤ, val P k x + P.e k = ((R.t : ℚ) + 1) / 2 + z := by
  obtain ⟨c, hc⟩ := R.t_odd
  have hc' : (R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  obtain ⟨e, he⟩ := P.e_int k
  rcases x with i | i | ⟨⟨i, hi⟩, a⟩ <;> simp only [val]
  · obtain ⟨z, hz⟩ := P.v_int i
    exact ⟨z + e - c - 1, by rw [hz, he, hc']; push_cast; ring⟩
  · obtain ⟨z, hz⟩ := P.b_int i
    exact ⟨-z + e - c - 1, by rw [hz, he, hc']; push_cast; ring⟩
  · obtain ⟨z, hz⟩ := P.e_int i
    exact ⟨-z + e - 1 - a.1, by rw [hz, he]; push_cast; ring⟩

theorem step_rule (k : Fin R.m) (x : ℚ) (s : Bool) :
    (∃ y : Idx R (k + 1), val P _ y + P.e k = x ∧ sgn R _ y = s) ↔
      (x ∈ block R.t ∧ s = true) ∨ (0 < x ∧ ∃ y : Idx R k, val P _ y + P.e k = x ∧ sgn R _ y = s) ∨
        (x < 0 ∧ ∃ y : Idx R k, val P _ y + P.e k = x ∧ sgn R _ y = !s) := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have hblock : ∀ x, x ∈ block R.t ↔ ∃ a : Fin R.t, ((R.t : ℚ) - 1) / 2 - (a.1 : ℚ) = x := by
    intro x
    simp [block, Fin.exists_iff]
  have pv : ∀ i, 0 < P.v i + P.e k := fun i => by
    have := neg_b_lt_v P i k; have := P.gap_be k; linarith
  have pe : ∀ (i : Fin R.m), i.1 < k.1 → ∀ a : Fin R.t, 0 < -P.e i + ((R.t : ℚ) - 1) / 2 - (a.1 : ℚ) + P.e k :=
    fun i hi a => by
      have := gap_of_lt P hi; have := P.gap_be k; have := cast_bounds a; linarith
  have s1 : ∀ i : Fin R.m, i.1 ≤ k.1 → 0 < -P.b i + P.e k ∧
      sgn R (k + 1) (.inr (.inl i)) = sgn R k (.inr (.inl i)) := fun i h => by
    have := gap_of_le P h
    exact ⟨by linarith, by simp [sgn, h, Nat.le_succ_of_le h]⟩
  have s2 : ∀ i : Fin R.m, k.1 < i.1 → -P.b i + P.e k < 0 ∧
      sgn R k (.inr (.inl i)) = !sgn R (k + 1) (.inr (.inl i)) := fun i h => by
    have := gap_of_lt P h
    refine ⟨by linarith, ?_⟩
    simp only [sgn, ← decide_not, decide_eq_decide, Nat.even_iff]
    omega
  constructor
  · rintro ⟨i | i | ⟨⟨i, hi⟩, a⟩, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨pv i, .inl i, rfl, rfl⟩)
    · rcases le_or_gt i.1 k.1 with h | h
      · exact Or.inr (Or.inl ⟨(s1 i h).1, .inr (.inl i), rfl, (s1 i h).2.symm⟩)
      · exact Or.inr (Or.inr ⟨(s2 i h).1, .inr (.inl i), rfl, (s2 i h).2⟩)
    · rcases (Nat.lt_succ_iff.1 hi).eq_or_lt with h | h
      · obtain rfl := Fin.ext h
        exact Or.inl ⟨(hblock _).2 ⟨a, by simp only [val]; ring⟩, rfl⟩
      · exact Or.inr (Or.inl ⟨pe i h a, .inr (.inr ⟨⟨i, h⟩, a⟩), rfl, rfl⟩)
  · rintro (⟨hx, rfl⟩ | ⟨hx, i | i | ⟨⟨i, hi⟩, a⟩, rfl, rfl⟩ | ⟨hx, i | i | ⟨⟨i, hi⟩, a⟩, rfl, hs⟩)
    · obtain ⟨a, rfl⟩ := (hblock x).1 hx
      exact ⟨.inr (.inr ⟨⟨k, by omega⟩, a⟩), by simp only [val]; ring, rfl⟩
    · exact ⟨.inl i, rfl, rfl⟩
    · rcases le_or_gt i.1 k.1 with h | h
      · exact ⟨.inr (.inl i), rfl, (s1 i h).2⟩
      · exact absurd hx (lt_asymm (s2 i h).1)
    · exact ⟨.inr (.inr ⟨⟨i, by omega⟩, a⟩), rfl, rfl⟩
    · exact absurd hx (lt_asymm (pv i))
    · rcases le_or_gt i.1 k.1 with h | h
      · exact absurd hx (lt_asymm (s1 i h).1)
      · exact ⟨.inr (.inl i), rfl, Bool.not_inj ((s2 i h).2.symm.trans hs)⟩
    · exact absurd hx (lt_asymm (pe i hi a))

end HC

variable {D : D7}

theorem mem_parA (j : ℕ) (τ : D.what₂.Tau) (x : ℚ) (s : Bool) :
    (x, s) ∈ parA (Ptw D) j τ ↔
      ∃ y : Idx D.R j, val (D.hc τ) j y + (if Odd j then -(1 / 2) else 0) = x ∧ sgn D.R j y = s := by
  unfold parA TPar.Dpar TPar.block
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists, Prod.mk.injEq, Finset.mem_range]
  constructor
  · rintro ⟨a, b, (⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩) | ⟨i, hi, x, ⟨a, ha, rfl⟩, rfl, rfl⟩, rfl, rfl⟩
    · exact ⟨.inl i, rfl, rfl⟩
    · exact ⟨.inr (.inl i), rfl, rfl⟩
    · exact ⟨.inr (.inr ⟨⟨i, hi⟩, ⟨a, ha⟩⟩), rfl, rfl⟩
  · rintro ⟨i | i | ⟨⟨i, hi⟩, a⟩, rfl, rfl⟩
    · exact ⟨_, _, Or.inl (Or.inl ⟨i, rfl, rfl⟩), rfl, rfl⟩
    · exact ⟨_, _, Or.inl (Or.inr ⟨i, rfl, rfl⟩), rfl, rfl⟩
    · exact ⟨_, _, Or.inr ⟨i, hi, _, ⟨a.1, a.2, rfl⟩, rfl, rfl⟩, rfl, rfl⟩

theorem expS_eq_alV (k : Fin D.R.m) (τ : D.what₂.Tau) : expS D k τ = alV D k τ := by
  unfold expS alV
  rcases Nat.even_or_odd (k : ℕ) with h | h
  · rw [if_pos h, if_pos h.add_one]
  · rw [if_neg (Nat.not_even_iff_odd.2 h), if_neg (Nat.not_odd_iff_even.2 h.add_one), sub_zero]

theorem expT_eq_alW (k : Fin D.R.m) (τ : D.what₂.Tau) : expT D k τ = alW D k τ := by
  unfold expT alW
  rcases Nat.even_or_odd (k : ℕ) with h | h
  · rw [if_pos h, if_pos h.add_one, sub_zero]
  · rw [if_neg (Nat.not_even_iff_odd.2 h), if_neg (Nat.not_odd_iff_even.2 h.add_one)]

theorem mem_lamS (k : Fin D.R.m) (τ : D.what₂.Tau) (x : ℚ) (s : Bool) :
    (x, s) ∈ lamS D k τ ↔ ∃ y : Idx D.R k, val (D.hc τ) _ y + (D.hc τ).e k = x ∧ sgn D.R _ y = s := by
  rw [lamS, mem_shiftPar, mem_parA]
  refine exists_congr fun y => and_congr_left' ?_
  unfold alW
  rcases Nat.even_or_odd (k : ℕ) with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), if_pos h.add_one]; constructor <;> intro h <;> linarith
  · rw [if_pos h, if_neg (Nat.not_odd_iff_even.2 h.add_one)]; constructor <;> intro h <;> linarith

theorem mem_lamT (k : Fin D.R.m) (τ : D.what₂.Tau) (x : ℚ) (s : Bool) :
    (x, s) ∈ lamT D k τ ↔ ∃ y : Idx D.R (k + 1), val (D.hc τ) _ y + (D.hc τ).e k = x ∧ sgn D.R _ y = s := by
  rw [lamT, mem_shiftPar, mem_parA]
  refine exists_congr fun y => and_congr_left' ?_
  unfold alV
  split_ifs <;> constructor <;> intro h <;> linarith

theorem card_lamS (k : Fin D.R.m) (τ : D.what₂.Tau) : (lamS D k τ).card = D.R.rankY k := by
  have : lamS D k τ = Finset.univ.image fun y : Idx D.R k => (val (D.hc τ) _ y + (D.hc τ).e k, sgn D.R _ y) := by
    ext ⟨x, s⟩
    simp only [mem_lamS, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
  rw [this, Finset.card_image_of_injective, Finset.card_univ, card_idx k.2.le]
  intro a b h
  exact val_injective _ _ (add_right_cancel (Prod.mk.inj h).1)

theorem exists_lists_chain (k : Fin D.R.m) (τ : D.what₂.Tau) :
    ∃ al be ga de : List ℚ, HypA D.R.t al be ga de ∧ (∀ e ∈ al ++ be ++ ga ++ de, ((D.R.t : ℚ) + 3) / 2 ≤ |e|) ∧
      lamS D k τ = signed (al ++ be) (ga ++ de) 0 ∧ lamT D k τ = signed (al ++ block D.R.t ++ de) (ga ++ be) 0 := by
  refine exists_lists (by have := D.R.three_m_lt_t; omega) ?_ ?_ ?_ ?_ ?_
  · exact ⟨(_, _), (mem_lamS k τ _ _).2 ⟨.inr (.inl k), rfl, rfl⟩⟩
  · intro x h1 h2
    obtain ⟨y, hy, hs⟩ := (mem_lamS k τ _ _).1 h1
    obtain ⟨y', hy', hs'⟩ := (mem_lamS k τ _ _).1 h2
    obtain rfl := val_injective _ _ (add_right_cancel (hy.trans hy'.symm))
    exact absurd (hs.symm.trans hs') (by simp)
  · intro x s h
    obtain ⟨y, rfl, -⟩ := (mem_lamS k τ _ _).1 h
    exact val_big _ k y
  · intro x s h
    obtain ⟨y, rfl, -⟩ := (mem_lamS k τ _ _).1 h
    exact val_int _ k y
  · intro x s
    simp only [mem_lamS, mem_lamT]
    exact step_rule _ k x s

theorem chainPar_iff_stepGap (k : Fin D.R.m) : ChainPar D k ↔ StepGap D k := by
  refine forall_congr' fun τ => ?_
  have hr : D.R.rankY ((k : ℕ) + 1) = D.R.rankY k + D.R.t := by simp only [Ranks.rankY]; ring
  simp only [expS_eq_alV, expT_eq_alW, eq_signed_iff (S := parA _ _ _)]
  rw [hr]
  constructor
  · rintro ⟨al, be, ga, de, ⟨hA, hG⟩, -, h1, h2⟩
    have h1' : lamS D k τ = _ := h1
    have h2' : lamT D k τ = _ := h2
    have := (hypG_iff hA.2.2.2.2.2.2.1 (h1' ▸ card_lamS k τ)).1 hG
    rwa [← h1', ← h2'] at this
  · intro h
    obtain ⟨al, be, ga, de, hA, hb, h1, h2⟩ := exists_lists_chain k τ
    refine ⟨al, be, ga, de, ⟨hA, (hypG_iff hA.2.2.2.2.2.2.1 (h1 ▸ card_lamS k τ)).2 ?_⟩, hb, h1, h2⟩
    rwa [← h1, ← h2]

end GlobalTheory.Chain.ItPairCompare

end
