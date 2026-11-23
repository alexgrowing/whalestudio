import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.PairLift.FromSigned

theorem cube_bound {n t N : ℕ} (h : n + t ≤ N) : (((n + t : ℕ) : ℝ)) ^ 3 ≤ 2 * (N : ℝ) ^ 3 := by
  have h1 : ((n + t : ℕ) : ℝ) ≤ N := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((n + t : ℕ) : ℝ) := by positivity
  have := pow_le_pow_left₀ h0 h1 3
  have : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  linarith

theorem gap_bound {n m N : ℕ} (hm : 2 * m ≤ n) (hn : n ≤ N) (hN : 1800 < N) :
    120 * (n : ℝ) * ((m : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  set y : ℝ := ((m : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hy0
  have y0 : 0 ≤ y := by positivity
  have hy : y ^ 2 = (m : ℝ) ^ 3 := by
    rw [hy0, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hM : (1800 : ℝ) < N := by exact_mod_cast hN
  have hmM : 2 * (m : ℝ) ≤ N := by exact_mod_cast hm.trans hn
  have hnM : (n : ℝ) ≤ N := by exact_mod_cast hn
  have m0 : (0 : ℝ) ≤ m := by positivity
  have n0 : (0 : ℝ) ≤ n := by positivity
  have h3 : (2 * (m : ℝ)) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hmM 3
  have h2 : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ n0 hnM 2
  have hsq : (60 * (n : ℝ) * y) ^ 2 ≤ ((N : ℝ) ^ 3) ^ 2 := by
    have e : (60 * (n : ℝ) * y) ^ 2 = 450 * (n : ℝ) ^ 2 * (2 * (m : ℝ)) ^ 3 := by
      rw [mul_pow, hy]; ring
    rw [e]
    have N0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have a1 : 450 * (n : ℝ) ^ 2 * (2 * (m : ℝ)) ^ 3 ≤ 450 * (N : ℝ) ^ 2 * (N : ℝ) ^ 3 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h3 (by positivity) (by positivity)
    have a2 : 450 * (N : ℝ) ^ 2 * (N : ℝ) ^ 3 ≤ ((N : ℝ) ^ 3) ^ 2 := by
      have : 450 * (N : ℝ) ^ 2 * (N : ℝ) ^ 3 = 450 * (N : ℝ) ^ 5 := by ring
      rw [this]
      have : ((N : ℝ) ^ 3) ^ 2 = (N : ℝ) * (N : ℝ) ^ 5 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hle : 60 * (n : ℝ) * y ≤ (N : ℝ) ^ 3 := by
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  linarith

end GlobalTheory.PairLift.FromSigned

namespace GlobalTheory.PairLift.FromSigned

def lst (P : SPar) (c : ℚ) (s : Bool) (p : ℚ → Prop) [DecidablePred p] : List ℚ :=
  GlobalTheory.SignedHC.descList ((P.filter fun x => x.2 = s ∧ p (x.1 - c)).image fun x => x.1 - c)

theorem mem_lst {P : SPar} {c : ℚ} {s : Bool} {p : ℚ → Prop} [DecidablePred p] {e : ℚ} :
    e ∈ lst P c s p ↔ (e + c, s) ∈ P ∧ p e := by
  simp only [lst, GlobalTheory.SignedHC.mem_descList, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨x, s'⟩, ⟨hx, h1, hp⟩, rfl⟩
    simp only at h1 hp
    subst h1
    simpa using And.intro hx hp
  · rintro ⟨h, hp⟩
    exact ⟨(e + c, s), ⟨h, rfl, by simpa using hp⟩, by simp⟩

theorem lst_pairwise (P : SPar) (c : ℚ) (s : Bool) (p : ℚ → Prop) [DecidablePred p] :
    (lst P c s p).Pairwise (· > ·) := GlobalTheory.SignedHC.pairwise_descList _

theorem mem_blockList {t : ℕ} {e : ℚ} : e ∈ Formalism.BasicNotions.TH.block t ↔ ∃ a : ℕ, a < t ∧ e = ((t : ℚ) - 1) / 2 - a := by
  simp only [Formalism.BasicNotions.TH.block, eq_comm (a := e)]
  simp

theorem sub_mem_blockList {t : ℕ} {y c' : ℚ} : y - c' ∈ Formalism.BasicNotions.TH.block t ↔ y ∈ TPar.block c' t := by
  rw [mem_blockList, GlobalTheory.SignedHC.mem_block]
  exact exists_congr fun a => and_congr_right fun _ => ⟨fun e => by linarith, fun e => by linarith⟩

theorem mem_move {P : SPar} {c c' y : ℚ} {s : Bool} (hc : ∀ x ∈ P, x.1 ≠ c) :
    (y, s) ∈ P.image (fun x => (x.1 - c + c', if x.1 < c then !x.2 else x.2)) ↔
      (0 < y - c' ∧ (y - c' + c, s) ∈ P) ∨ (y - c' < 0 ∧ (y - c' + c, !s) ∈ P) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨x, s0⟩, hx, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have e1 : x - c + c' - c' + c = x := by ring
    rw [e1]
    by_cases h : x < c
    · right; simp only [h, if_true, Bool.not_not]; exact ⟨by linarith, hx⟩
    · left
      have : c < x := lt_of_le_of_ne (not_lt.1 h) (fun e => hc _ hx e.symm)
      simp only [h, if_false]; exact ⟨by linarith, hx⟩
  · rintro (⟨h, hx⟩ | ⟨h, hx⟩)
    · refine ⟨_, hx, ?_⟩
      have : ¬ (y - c' + c < c) := by linarith
      simp only [this, if_false, Prod.mk.injEq, and_true]; ring
    · refine ⟨_, hx, ?_⟩
      have : y - c' + c < c := by linarith
      simp only [this, if_true, Bool.not_not, Prod.mk.injEq, and_true]; ring

theorem signed_zero_shift {l₁ l₂ : List ℚ} {c : ℚ} {x : ℚ × Bool} (h : x ∈ signed l₁ l₂ 0) :
    (x.1 + c, x.2) ∈ signed l₁ l₂ c := by
  obtain ⟨a, s⟩ := x
  rw [GlobalTheory.Chain.ItPairCompare.mem_signed] at h ⊢
  simpa using h

theorem card_signed_c {l₁ l₂ : List ℚ} {c : ℚ} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) :
    (signed l₁ l₂ c).card = l₁.length + l₂.length := by
  have e : signed l₁ l₂ c = (signed l₁ l₂ 0).image fun x => (x.1 + c, x.2) := by
    ext ⟨a, s⟩
    simp only [Finset.mem_image, Prod.exists, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨a - c, s, ?_, by ring, rfl⟩
      rw [GlobalTheory.Chain.ItPairCompare.mem_signed] at h ⊢
      simpa using h
    · rintro ⟨b, s', h, rfl, rfl⟩
      exact signed_zero_shift (x := (b, s')) h
  rw [e, Finset.card_image_of_injective _ (fun x y h => by
    simp only [Prod.mk.injEq, add_left_inj] at h; exact Prod.ext h.1 h.2),
    GlobalTheory.Chain.ItPairCompare.card_signed h₁ h₂]

end GlobalTheory.PairLift.FromSigned

namespace GlobalTheory.PairLift.FromSigned

theorem real_gap {h : ℝ} {q : ℚ} {N : ℕ} (hh : h ≤ 2 * (N : ℝ) ^ 3) (hq : 2 * (N : ℚ) ^ 3 < |q|) : h < |(q : ℝ)| := by
  have := (Rat.cast_lt (K := ℝ)).2 hq
  push_cast at this
  linarith

theorem thetaPar_partner : ∀ (t : ℕ) (b : Bool) (c c' : ℚ) (P : SPar) (N : ℕ), 1 ≤ t → P.Nonempty →
    GlobalTheory.SignedHC.IsRegular P → GlobalTheory.SignedHC.InCoset (c + ((t : ℚ) + 1) / 2) (GlobalTheory.SignedHC.entries P) →
    GlobalTheory.SignedHC.FarFrom c (((t : ℚ) + 1) / 2) P → P.card + t ≤ N → 1800 < N → GapOver P (2 * (N : ℚ) ^ 3) →
    GapOver (partner t b c c' P) (2 * (N : ℚ) ^ 3) → ThetaPar t P (partner t b c c' P) c c' := by
  intro t b c c' P N ht hne hreg hco hfar hcard hN hg hg'
  have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have hc : ∀ x ∈ P, x.1 ≠ c := fun x hx e => by
    have := hfar x.1 (GlobalTheory.SignedHC.fst_mem_entries hx)
    rw [e, sub_self, abs_zero] at this
    linarith
  set al := lst P c true (0 < ·) with hal
  set be := lst P c true (· < 0) with hbe
  set ga := lst P c false (0 < ·) with hga
  set de := lst P c false (· < 0) with hde
  have ha : ∀ e, e ∈ al ↔ (e + c, true) ∈ P ∧ 0 < e := fun e => mem_lst
  have hb : ∀ e, e ∈ be ↔ (e + c, true) ∈ P ∧ e < 0 := fun e => mem_lst
  have hg1 : ∀ e, e ∈ ga ↔ (e + c, false) ∈ P ∧ 0 < e := fun e => mem_lst
  have hd : ∀ e, e ∈ de ↔ (e + c, false) ∈ P ∧ e < 0 := fun e => mem_lst
  have pa : al.Pairwise (· > ·) := lst_pairwise _ _ _ _
  have pb : be.Pairwise (· > ·) := lst_pairwise _ _ _ _
  have pg : ga.Pairwise (· > ·) := lst_pairwise _ _ _ _
  have pd : de.Pairwise (· > ·) := lst_pairwise _ _ _ _
  have inj : ∀ x, (x, true) ∈ P → (x, false) ∈ P → False := fun x h1 h2 => by
    have := hreg _ h1 _ h2 rfl; simp at this
  have hP : P = signed (al ++ be) (ga ++ de) c := by
    ext ⟨x, s⟩
    rw [GlobalTheory.Chain.ItPairCompare.mem_signed]
    simp only [List.mem_append, ha, hb, hg1, hd, sub_add_cancel]
    by_cases hx : (x, s) ∈ P
    · have h0 : x - c ≠ 0 := sub_ne_zero.2 (hc _ hx)
      rcases lt_or_gt_of_ne h0 with h | h <;> cases s <;> simp [hx, h]
    · cases s <;> simp [hx]
  have nd : ∀ {l : List ℚ}, l.Pairwise (· > ·) → l.Nodup := fun h => h.imp fun h => h.ne'
  have hnd : (al ++ be ++ ga ++ de).Nodup := by
    simp only [List.nodup_append, nd pa, nd pb, nd pg, nd pd, List.mem_append, ha, hb, hg1, hd, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro a h1 b h2 rfl; exact lt_asymm h1.2 h2.2
    · rintro a (h1 | h1) b h2 rfl <;> exact inj _ h1.1 h2.1
    · rintro a ((h1 | h1) | h1) b h2 rfl
      · exact inj _ h1.1 h2.1
      · exact inj _ h1.1 h2.1
      · exact lt_asymm h1.2 h2.2
  have hnd' := hnd
  rw [List.append_assoc (al ++ be)] at hnd'
  have h₁ := hnd'.of_append_left
  have h₂ := hnd'.of_append_right
  have hn : al.length + be.length + ga.length + de.length = P.card := by
    conv_rhs => rw [hP]
    rw [card_signed_c h₁ h₂]; simp only [List.length_append]; omega
  have all : ∀ e ∈ al ++ be ++ ga ++ de, ∃ s, (e + c, s) ∈ P := by
    intro e he
    simp only [List.mem_append, ha, hb, hg1, hd] at he
    rcases he with ((h | h) | h) | h <;> exact ⟨_, h.1⟩
  have hA : HypA t al be ga de := by
    refine ⟨ht, ?_, pa, pb, pg, pd, hnd, ?_, ?_, ?_, ?_⟩
    · obtain ⟨⟨x, s⟩, hx⟩ := hne
      rw [hP, GlobalTheory.Chain.ItPairCompare.mem_signed] at hx
      rcases hx with ⟨-, hx⟩ | ⟨-, hx⟩
      · have := List.length_pos_of_mem hx
        rw [List.length_append] at this; omega
      · have := List.length_pos_of_mem hx
        rw [List.length_append] at this; omega
    · intro e he
      simp only [List.mem_append, ha, hg1] at he
      rcases he with h | h <;> exact h.2
    · intro e he
      simp only [List.mem_append, hb, hd] at he
      rcases he with h | h <;> exact h.2
    · intro e he
      obtain ⟨s, h⟩ := all e he
      obtain ⟨z, hz⟩ := hco _ (GlobalTheory.SignedHC.fst_mem_entries h)
      exact ⟨z, by simp only at hz; linarith⟩
    · intro e he
      obtain ⟨s, h⟩ := all e he
      have := hfar _ (GlobalTheory.SignedHC.fst_mem_entries h)
      simpa using this
  have hnt : al.length + be.length + ga.length + de.length + t ≤ N := by omega
  have gapP : ∀ x ∈ signed (al ++ be) (ga ++ de) 0, ∀ y ∈ signed (al ++ be) (ga ++ de) 0, x.2 ≠ y.2 →
      2 * (N : ℚ) ^ 3 < |x.1 - y.1| := by
    intro x hx y hy hs
    have h1 : (x.1 + c, x.2) ∈ P := by rw [hP]; exact signed_zero_shift hx
    have h2 : (y.1 + c, y.2) ∈ P := by rw [hP]; exact signed_zero_shift hy
    have := hg _ h1 _ h2 hs
    simpa using this
  have G1 : GapGt (lamA al be ga de) (((al.length + be.length + ga.length + de.length + t : ℕ) : ℝ) ^ 3) := by
    unfold GapGt lamA
    refine (GlobalTheory.Chain.ItPairCompare.cross_iff (l₁ := al ++ be) (l₂ := ga ++ de) (by simp) (by simp)
      (fun z => (((al.length + be.length + ga.length + de.length + t : ℕ) : ℝ) ^ 3) < |(z : ℝ)|)).2 ?_
    intro x hx y hy hs
    exact real_gap (cube_bound hnt) (gapP x hx y hy hs)
  have G3 : GapGe (lamA al be ga de) (120 * ((al.length + be.length + ga.length + de.length : ℕ) : ℝ) *
      ((min (al.length + be.length) (ga.length + de.length) : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by
    unfold GapGe lamA
    refine (GlobalTheory.Chain.ItPairCompare.cross_iff (l₁ := al ++ be) (l₂ := ga ++ de) (by simp) (by simp)
      (fun z => 120 * ((al.length + be.length + ga.length + de.length : ℕ) : ℝ) *
      ((min (al.length + be.length) (ga.length + de.length) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ |(z : ℝ)|)).2 ?_
    intro x hx y hy hs
    refine (real_gap (gap_bound (by omega) (by omega) hN) (gapP x hx y hy hs)).le
  refine ⟨al, be, ga, de, hP, ?_⟩
  cases b
  ·
    have hP' : partner t false c c' P = signed (al ++ de) (ga ++ block t ++ be) c' := by
      ext ⟨y, s⟩
      rw [partner, Finset.mem_union, mem_move hc, GlobalTheory.Chain.ItPairCompare.mem_signed]
      simp only [Finset.mem_image, List.mem_append, ha, hb, hg1, hd, sub_mem_blockList]
      cases s <;> simp <;> tauto
    right
    refine ⟨⟨hA, G1, ?_, G3⟩, hP'⟩
    unfold GapGt lamM'
    have hl : (block t).length = t := by simp [block]
    refine (GlobalTheory.Chain.ItPairCompare.cross_iff (l₁ := al ++ de) (l₂ := ga ++ block t ++ be) (by simp)
      (by simp [hl] <;> omega)
      (fun z => (((al.length + be.length + ga.length + de.length + t : ℕ) : ℝ) ^ 3) < |(z : ℝ)|)).2 ?_
    intro x hx y hy hs
    have h1 : (x.1 + c', x.2) ∈ partner t false c c' P := by rw [hP']; exact signed_zero_shift hx
    have h2 : (y.1 + c', y.2) ∈ partner t false c c' P := by rw [hP']; exact signed_zero_shift hy
    have := hg' _ h1 _ h2 hs
    exact real_gap (cube_bound hnt) (by simpa using this)
  ·
    have hP' : partner t true c c' P = signed (al ++ block t ++ de) (ga ++ be) c' := by
      ext ⟨y, s⟩
      rw [partner, Finset.mem_union, mem_move hc, GlobalTheory.Chain.ItPairCompare.mem_signed]
      simp only [Finset.mem_image, List.mem_append, ha, hb, hg1, hd, sub_mem_blockList]
      cases s <;> simp <;> tauto
    left
    refine ⟨⟨hA, G1, ?_, G3⟩, hP'⟩
    unfold GapGt lamA'
    have hl : (block t).length = t := by simp [block]
    refine (GlobalTheory.Chain.ItPairCompare.cross_iff (l₁ := al ++ block t ++ de) (l₂ := ga ++ be) (by simp [hl] <;> omega)
      (by simp <;> omega)
      (fun z => (((al.length + be.length + ga.length + de.length + t : ℕ) : ℝ) ^ 3) < |(z : ℝ)|)).2 ?_
    intro x hx y hy hs
    have h1 : (x.1 + c', x.2) ∈ partner t true c c' P := by rw [hP']; exact signed_zero_shift hx
    have h2 : (y.1 + c', y.2) ∈ partner t true c c' P := by rw [hP']; exact signed_zero_shift hy
    have := hg' _ h1 _ h2 hs
    exact real_gap (cube_bound hnt) (by simpa using this)

end GlobalTheory.PairLift.FromSigned
