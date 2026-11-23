import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

noncomputable section

open Zc.Cos

namespace PositivityTheory.Groth.AltC

theorem filter_mem_eq_of_sublist {α : Type*} [DecidableEq α] {l m : List α} (hs : l.Sublist m)
    (hm : m.Nodup) : m.filter (fun x => decide (x ∈ l)) = l := by
  induction hs with
  | slnil => rfl
  | @cons l m a hs ih =>
    have ha : a ∉ l := fun h => (List.nodup_cons.1 hm).1 (hs.subset h)
    rw [List.filter_cons_of_neg (by simpa using ha)]
    exact ih (List.nodup_cons.1 hm).2
  | @cons_cons l m a hs ih =>
    rw [List.filter_cons_of_pos (by simp)]
    congr 1
    rw [← ih (List.nodup_cons.1 hm).2]
    apply List.filter_congr
    intro x hx
    have : x ≠ a := fun h => (List.nodup_cons.1 hm).1 (h ▸ hx)
    simp [this, hx]

theorem mem_sub {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) (x : α) :
    x ∈ sub W c i ↔ ∃ p, c p = i ∧ W.get p = x := by
  unfold sub
  simp [List.mem_map, List.mem_filter, List.mem_finRange]

theorem mem_sub_self {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (p : Fin W.length) :
    W.get p ∈ sub W c (c p) :=
  (mem_sub W c (c p) _).2 ⟨p, rfl, rfl⟩

theorem sub_sublist {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    (sub W c i).Sublist W := by
  unfold sub
  have := (List.filter_sublist (p := fun p => decide (c p = i)) (l := List.finRange W.length)).map W.get
  rwa [← List.ofFn_eq_map, List.ofFn_get] at this

open Classical in

theorem shuffleCount_eq {α : Type*} {h : ℕ} (W : List α) (D : Fin h → List α) (hW : W.Nodup) :
    shuffleCount W D = if (∀ i, (D i).Sublist W) ∧ (∀ x ∈ W, ∃! i, x ∈ D i) then 1 else 0 := by
  unfold shuffleCount
  split_ifs with hc
  · rw [Finset.card_eq_one]
    choose c0 hc0 using fun p : Fin W.length => (hc.2 (W.get p) (List.get_mem W p)).exists
    have hu : ∀ p y, W.get p ∈ D y → y = c0 p := fun p y hy =>
      (hc.2 (W.get p) (List.get_mem W p)).unique hy (hc0 p)
    refine ⟨c0, ?_⟩
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hcs
      funext p
      have := mem_sub_self W c p
      rw [hcs (c p)] at this
      exact hu p (c p) this
    · intro hcc i
      rw [hcc]
      have : sub W c0 i = W.filter (fun x => decide (x ∈ D i)) := by
        unfold sub
        conv_rhs => rw [← List.ofFn_get W, List.ofFn_eq_map, List.filter_map]
        congr 1
        apply List.filter_congr
        intro p _
        simp only [Function.comp, decide_eq_decide]
        exact ⟨fun h => h ▸ hc0 p, fun h => (hu p i h).symm⟩
      rw [this, filter_mem_eq_of_sublist (hc.1 i) hW]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hcs
    apply hc
    refine ⟨fun i => hcs i ▸ sub_sublist W c i, fun x hx => ?_⟩
    obtain ⟨p, rfl⟩ := List.get_of_mem hx
    refine ⟨c p, ?_, fun j hj => ?_⟩
    · show W.get p ∈ D (c p)
      rw [← hcs (c p)]; exact mem_sub_self W c p
    simp only at hj
    rw [← hcs j] at hj
    obtain ⟨q, hq, hqp⟩ := (mem_sub W c j _).1 hj
    have := hW.get_inj_iff.1 hqp
    subst this
    exact hq.symm

theorem cond_map {β α : Type*} {h : ℕ} (f : β → α) (hf : Function.Injective f) (w : List β)
    (E : Fin h → List β) :
    ((∀ i, ((E i).map f).Sublist (w.map f)) ∧ (∀ x ∈ w.map f, ∃! i, x ∈ (E i).map f)) ↔
      ((∀ i, (E i).Sublist w) ∧ (∀ y ∈ w, ∃! i, y ∈ E i)) := by
  have hs : ∀ i, ((E i).map f).Sublist (w.map f) ↔ (E i).Sublist w := by
    intro i
    refine ⟨fun H => ?_, fun H => H.map f⟩
    obtain ⟨l', hl', he⟩ := List.sublist_map_iff.1 H
    rwa [List.map_injective_iff.2 hf he]
  simp only [hs, List.forall_mem_map, List.mem_map_of_injective hf]

def wN (L : ℕ) (T : Finset ℕ) : List ℕ :=
  ((List.range L).filter (fun x => decide (x ∈ T))).reverse ++ (List.range L).filter (fun x => decide (x ∉ T))

theorem mem_wN {L x : ℕ} {T : Finset ℕ} : x ∈ wN L T ↔ x < L := by
  unfold wN
  by_cases hx : x ∈ T <;> simp [hx]

theorem nodup_wN (L : ℕ) (T : Finset ℕ) : (wN L T).Nodup := by
  unfold wN
  rw [List.nodup_append]
  refine ⟨List.nodup_reverse.2 ((List.nodup_range).filter _), (List.nodup_range).filter _, ?_⟩
  intro a ha c hc hac
  subst hac
  simp at ha hc
  exact hc.2 ha.2

theorem sublist_of_lt {l m : List ℕ} (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·))
    (hs : ∀ x ∈ l, x ∈ m) : l.Sublist m :=
  List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hl.nodup hs) hl hm

theorem run_sublist {L b l : ℕ} {T : Finset ℕ} (hbl : b + l ≤ L) :
    ((List.range' b l).reverse).Sublist (wN L T) ↔ ∀ x, b < x → x < b + l → x ∈ T := by
  have hA : ((List.range L).filter (fun x => decide (x ∈ T))).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hB : ((List.range L).filter (fun x => decide (x ∉ T))).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  constructor
  · intro hs x hbx hxl
    by_contra hxT
    obtain ⟨F1, F2, hE, h1, h2⟩ := List.sublist_append_iff.1 hs
    have hxE : x ∈ (List.range' b l).reverse := by
      simp only [List.mem_reverse, List.mem_range'_1]; omega
    have hbE : b ∈ (List.range' b l).reverse := by
      simp only [List.mem_reverse, List.mem_range'_1]; omega
    have hpw : (F1 ++ F2).Pairwise (fun a c => c < a) := by
      rw [← hE]; exact List.pairwise_reverse.2 List.pairwise_lt_range'
    have hx2 : x ∈ F2 := by
      rw [hE] at hxE
      rcases List.mem_append.1 hxE with h | h
      · have := h1.subset h
        simp at this
        exact absurd this.2 hxT
      · exact h
    have hb2 : b ∈ F2 := by
      rw [hE] at hbE
      rcases List.mem_append.1 hbE with h | h
      · have := (List.pairwise_append.1 hpw).2.2 b h x hx2
        omega
      · exact h
    have hinc : F2.Pairwise (· < ·) := hB.sublist h2
    have hdec := (List.pairwise_append.1 hpw).2.1
    rcases F2 with _ | ⟨y, _ | ⟨z, t⟩⟩
    · simp at hx2
    · simp at hx2 hb2
      omega
    · have a1 := (List.pairwise_cons.1 hinc).1 z (by simp)
      have a2 := (List.pairwise_cons.1 hdec).1 z (by simp)
      omega
  · intro hT
    by_cases hb : b ∈ T
    · have : (List.range' b l).Sublist ((List.range L).filter (fun x => decide (x ∈ T))) := by
        refine sublist_of_lt List.pairwise_lt_range' hA fun x hx => ?_
        rw [List.mem_range'_1] at hx
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rcases Nat.eq_or_lt_of_le hx.1 with h | h
        · exact h ▸ hb
        · exact hT x h hx.2
      exact (List.reverse_sublist.2 this).trans (List.sublist_append_left _ _)
    · rcases l with _ | m
      · simp
      rw [List.range'_succ, List.reverse_cons]
      have : (List.range' (b + 1) m).Sublist ((List.range L).filter (fun x => decide (x ∈ T))) := by
        refine sublist_of_lt List.pairwise_lt_range' hA fun x hx => ?_
        rw [List.mem_range'_1] at hx
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨by omega, hT x (by omega) (by omega)⟩
      refine (List.reverse_sublist.2 this).append (List.singleton_sublist.2 ?_)
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, hb⟩

def Cond (L : ℕ) (T : Finset ℕ) {h : ℕ} (b l : Fin h → ℕ) : Prop :=
  (∀ i, ((List.range' (b i) (l i)).reverse).Sublist (wN L T)) ∧
    (∀ x ∈ wN L T, ∃! i, x ∈ (List.range' (b i) (l i)).reverse)

theorem cond_iff {L : ℕ} {T : Finset ℕ} {h : ℕ} {b l : Fin h → ℕ} (hl : ∀ i, 0 < l i) :
    Cond L T b l ↔ (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧
      (∀ i x, b i < x → x < b i + l i → x ∈ T) := by
  have hmem : ∀ i x, x ∈ (List.range' (b i) (l i)).reverse ↔ b i ≤ x ∧ x < b i + l i := by
    intro i x; simp [List.mem_range'_1]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : ∀ i, b i + l i ≤ L := fun i => by
      have hi := hl i
      have := (h1 i).subset ((hmem i (b i + l i - 1)).2 ⟨by omega, by omega⟩)
      rw [mem_wN] at this
      omega
    refine ⟨hb, fun x hx => ?_, fun i => (run_sublist (hb i)).1 (h1 i)⟩
    obtain ⟨i, hi, hu⟩ := h2 x (mem_wN.2 hx)
    exact ⟨i, (hmem i x).1 hi, fun j hj => hu j ((hmem j x).2 hj)⟩
  · rintro ⟨hb, hP, hT⟩
    refine ⟨fun i => (run_sublist (hb i)).2 (hT i), fun x hx => ?_⟩
    obtain ⟨i, hi, hu⟩ := hP x (mem_wN.1 hx)
    exact ⟨i, (hmem i x).2 hi, fun j hj => hu j ((hmem j x).1 hj)⟩

end PositivityTheory.Groth.AltC

namespace PositivityTheory.Groth.AltC

open Classical in

theorem altSumN (L : ℕ) (hL : 0 < L) (s : Finset (Finset (Fin L))) (hs : ∀ S, S ∈ s ↔ ∀ a ∈ S, (a : ℕ) ≠ 0)
    {h : ℕ} (b l : Fin h → ℕ) (hl : ∀ i, 0 < l i) (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, f S = (-1) ^ S.card * if Cond L (S.map Fin.valEmbedding) b l then 1 else 0) :
    ∑ S ∈ s, f S = if h = 1 ∧ ∀ i, b i = 0 ∧ l i = L then (-1) ^ (L - 1) else 0 := by
  have hcond : ∀ S : Finset (Fin L), Cond L (S.map Fin.valEmbedding) b l ↔ (∀ i, b i + l i ≤ L) ∧
      (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧
      (∀ i x, b i < x → x < b i + l i → ∃ a ∈ S, (a : ℕ) = x) := by
    intro S
    rw [cond_iff hl]
    simp [Finset.mem_map]
  by_cases hB : (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i)
  swap
  · rw [if_neg]
    · apply Finset.sum_eq_zero
      intro S _
      rw [hf, if_neg, mul_zero]
      rw [hcond]
      exact fun H => hB ⟨H.1, H.2.1⟩
    · rintro ⟨rfl, hbl⟩
      apply hB
      refine ⟨fun i => by rw [(hbl i).1, (hbl i).2]; simp, fun x hx => ⟨0, ?_, fun j _ => Subsingleton.elim _ _⟩⟩
      show b 0 ≤ x ∧ x < b 0 + l 0
      rw [(hbl 0).1, (hbl 0).2]
      exact ⟨Nat.zero_le _, by omega⟩
  obtain ⟨hb, hP⟩ := hB
  by_cases hz : ∃ j, b j ≠ 0
  · obtain ⟨j, hj⟩ := hz
    rw [if_neg (by rintro ⟨_, hbl⟩; exact hj (hbl j).1)]
    have hjL : b j < L := by have := hb j; have := hl j; omega
    set a : Fin L := ⟨b j, hjL⟩ with ha_def
    have hint : ∀ i x, b i < x → x < b i + l i → x ≠ (a : ℕ) := by
      intro i x h1 h2 hx
      rw [ha_def] at hx
      simp only at hx
      subst hx
      obtain ⟨k, _, hu⟩ := hP (b j) hjL
      have e1 := hu i ⟨h1.le, h2⟩
      have e2 := hu j ⟨le_rfl, by have := hl j; omega⟩
      rw [← e2] at e1
      subst e1
      omega
    have hg : ∀ S : Finset (Fin L), (if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding =
        (if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding := fun _ => rfl
    have hc : ∀ S : Finset (Fin L), Cond L ((if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding) b l ↔
        Cond L (S.map Fin.valEmbedding) b l := by
      intro S
      rw [hcond, hcond]
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => forall_congr' fun x =>
        imp_congr_right fun h1 => imp_congr_right fun h2 => ?_
      have hxa := hint i x h1 h2
      constructor
      · rintro ⟨a', ha', rfl⟩
        refine ⟨a', ?_, rfl⟩
        split_ifs at ha' with haS
        · exact Finset.mem_of_mem_erase ha'
        · rcases Finset.mem_insert.1 ha' with h | h
          · exact absurd (congrArg Fin.val h) hxa
          · exact h
      · rintro ⟨a', ha', rfl⟩
        refine ⟨a', ?_, rfl⟩
        have : a' ≠ a := fun h => hxa (congrArg Fin.val h)
        split_ifs
        · exact Finset.mem_erase.2 ⟨this, ha'⟩
        · exact Finset.mem_insert_of_mem ha'
    have hcard : ∀ S : Finset (Fin L), (-1 : ℤ) ^ (if a ∈ S then S.erase a else insert a S).card =
        -(-1) ^ S.card := by
      intro S
      split_ifs with haS
      · rw [Finset.card_erase_of_mem haS]
        have : 0 < S.card := Finset.card_pos.2 ⟨a, haS⟩
        obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by omega⟩
        rw [hn, pow_succ]
        simp
      · rw [Finset.card_insert_of_notMem haS, pow_succ]
        ring
    refine Finset.sum_involution (fun S _ => if a ∈ S then S.erase a else insert a S) ?_ ?_ ?_ ?_
    · intro S _
      rw [hf, hf, hcard, hc]
      ring
    · intro S _ _
      split_ifs with haS
      · exact fun h => Finset.notMem_erase a S (by rw [h]; exact haS)
      · exact fun h => haS (by rw [← h]; exact Finset.mem_insert_self a S)
    · intro S hS
      rw [hs] at hS ⊢
      intro x hx
      split_ifs at hx
      · exact hS x (Finset.mem_of_mem_erase hx)
      · rcases Finset.mem_insert.1 hx with rfl | h
        · exact hj
        · exact hS x h
    · intro S _
      by_cases haS : a ∈ S
      · simp [haS, Finset.insert_erase]
      · simp [haS]
  · push Not at hz
    obtain ⟨i0, _, hu⟩ := hP 0 hL
    have hall : ∀ i, i = i0 := fun i => hu i ⟨by rw [hz i], by rw [hz i]; have := hl i; omega⟩
    have hh : h = 1 := by
      have : Fintype.card (Fin h) = 1 := Fintype.card_eq_one_iff.2 ⟨i0, hall⟩
      simpa using this
    subst hh
    have hlL : ∀ i, l i = L := by
      intro i
      rw [hall i]
      have := hb i0
      rw [hz] at this
      by_contra hne
      obtain ⟨k, hk, _⟩ := hP (l i0) (by omega)
      rw [hall k, hz] at hk
      omega
    rw [if_pos ⟨rfl, fun i => ⟨hz i, hlL i⟩⟩]
    obtain ⟨S0, hS0def⟩ : ∃ S0 : Finset (Fin L), S0 = Finset.univ.filter (fun a : Fin L => (a : ℕ) ≠ 0) := ⟨_, rfl⟩
    have hS0 : S0 ∈ s := (hs S0).2 (fun a ha => by rw [hS0def] at ha; exact (Finset.mem_filter.1 ha).2)
    rw [Finset.sum_eq_single_of_mem S0 hS0]
    · rw [hf, if_pos, mul_one]
      · congr 1
        obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
        have : S0 = Finset.univ.erase 0 := by
          ext x
          rw [hS0def, Finset.mem_filter, Finset.mem_erase]
          simp only [Finset.mem_univ, true_and, and_true]
          exact ⟨fun hx h => hx (by rw [h]; rfl), fun hx h => hx (Fin.ext (by simpa using h))⟩
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      · rw [hcond]
        refine ⟨hb, hP, fun i x h1 h2 => ⟨⟨x, by rw [hz, hlL] at h2; simpa using h2⟩, ?_, rfl⟩⟩
        rw [hz] at h1
        simp [hS0def]
        omega
    · intro S hS hne
      rw [hf, if_neg, mul_zero]
      rw [hcond]
      rintro ⟨_, _, hT⟩
      apply hne
      ext x
      simp only [hS0def, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact (hs S).1 hS x hx
      · intro hx0
        obtain ⟨a', ha', he⟩ := hT i0 x (by rw [hz]; omega) (by rw [hz, hlL]; simp)
        rwa [Fin.ext he] at ha'

end PositivityTheory.Groth.AltC

end
