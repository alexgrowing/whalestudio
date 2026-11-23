import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.MemCenterOfCommuteE

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

def Closed (P : Fin n × Fin n → Prop) : Prop := ∀ a b, P a → P b → a.2 = b.1 → P (a.1, b.2)

def IsLower (a : Fin n × Fin n) : Prop := a.2 < a.1

def IsDiag (a : Fin n × Fin n) : Prop := a.1 = a.2

def IsUpper (a : Fin n × Fin n) : Prop := a.1 < a.2

theorem closed_lower : Closed (IsLower (n := n)) := fun a b ha hb h => by
  simp only [IsLower] at *; rw [h] at ha; exact lt_trans hb ha

theorem closed_upper : Closed (IsUpper (n := n)) := fun a b ha hb h => by
  simp only [IsUpper] at *; rw [h] at ha; exact lt_trans ha hb

theorem closed_diag : Closed (IsDiag (n := n)) := fun a b ha hb h => by
  simp only [IsDiag] at *; rw [ha, h, hb]

theorem closed_true : Closed (fun _ : Fin n × Fin n => True) := fun _ _ _ _ _ => trivial

def wordSpan (P : Fin n × Fin n → Prop) (k : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ w : List (Fin n × Fin n), (∀ a ∈ w, P a) ∧ w.length = k ∧ word w = u}

theorem word_mem_wordSpan {P : Fin n × Fin n → Prop} {w : List (Fin n × Fin n)}
    (hw : ∀ a ∈ w, P a) : word w ∈ wordSpan P w.length :=
  Submodule.subset_span ⟨w, hw, rfl, rfl⟩

theorem e_mul_mem_wordSpan {P : Fin n × Fin n → Prop} {a : Fin n × Fin n} (ha : P a) {k : ℕ}
    {u : U n} (hu : u ∈ wordSpan P k) : e a * u ∈ wordSpan P (k + 1) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl, rfl⟩ := hx
    rw [← word_cons]
    refine word_mem_wordSpan (w := a :: w) ?_
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · exact hw b hb
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem mul_mem_wordSpan {P : Fin n × Fin n → Prop} {v : List (Fin n × Fin n)}
    (hv : ∀ a ∈ v, P a) {k : ℕ} {u : U n} (hu : u ∈ wordSpan P k) :
    word v * u ∈ wordSpan P (v.length + k) := by
  induction v with
  | nil => simpa using hu
  | cons a v ih =>
    rw [word_cons, mul_assoc, List.length_cons, show v.length + 1 + k = (v.length + k) + 1 by omega]
    exact e_mul_mem_wordSpan (hv a (List.mem_cons_self ..))
      (ih fun b hb => hv b (List.mem_cons_of_mem _ hb))

theorem commutator_mul_mem_wordSpan {P : Fin n × Fin n → Prop} (hP : Closed P)
    {a b : Fin n × Fin n} (ha : P a) (hb : P b) {l : List (Fin n × Fin n)} (hl : ∀ c ∈ l, P c) :
    (e a * e b - e b * e a) * word l ∈ wordSpan P (l.length + 1) := by
  rw [e_mul_sub_mul, sub_mul]
  refine Submodule.sub_mem _ ?_ ?_
  · split_ifs with h
    · rw [← word_cons]
      refine word_mem_wordSpan (w := (a.1, b.2) :: l) ?_
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hP a b ha hb h
      · exact hl c hc
    · simp
  · split_ifs with h
    · rw [← word_cons]
      refine word_mem_wordSpan (w := (b.1, a.2) :: l) ?_
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hP b a hb ha h
      · exact hl c hc
    · simp

theorem word_sub_word_mem_of_perm {P : Fin n × Fin n → Prop} (hP : Closed P)
    {w w' : List (Fin n × Fin n)} (h : w.Perm w') (hw : ∀ a ∈ w, P a) :
    word w - word w' ∈ wordSpan P (w.length - 1) := by
  induction h with
  | nil => simp
  | cons x h ih =>
    rename_i l₁ l₂
    rcases l₁ with _ | ⟨y, l₁⟩
    · rw [List.nil_perm.1 h]; simp
    · rw [show word (x :: y :: l₁) - word (x :: l₂) = e x * (word (y :: l₁) - word l₂) by
        rw [word_cons x, word_cons x, mul_sub], List.length_cons, Nat.add_sub_cancel]
      have := ih fun a ha => hw a (List.mem_cons_of_mem _ ha)
      simp only [List.length_cons, Nat.add_sub_cancel] at this
      exact e_mul_mem_wordSpan (hw x (List.mem_cons_self ..)) this
  | swap x y l =>
    rw [word_cons, word_cons, word_cons, word_cons, ← mul_assoc, ← mul_assoc, ← sub_mul]
    simp only [List.length_cons, Nat.add_sub_cancel]
    exact commutator_mul_mem_wordSpan hP (hw y (by simp)) (hw x (by simp))
      (fun c hc => hw c (by simp [hc]))
  | trans h₁ h₂ ih₁ ih₂ =>
    rw [← sub_add_sub_cancel]
    refine Submodule.add_mem _ (ih₁ hw) ?_
    rw [h₁.length_eq]
    exact ih₂ fun a ha => hw a (h₁.symm.subset ha)

def letters (n : ℕ) : List (Fin n × Fin n) :=
  let all := (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)
  all.filter (fun a => decide (a.2 < a.1)) ++ all.filter (fun a => decide (a.1 = a.2)) ++
    all.filter (fun a => decide (a.1 < a.2))

theorem mem_letters (a : Fin n × Fin n) : a ∈ letters n := by
  simp only [letters, List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and, decide_eq_true_eq]
  have hall : ∃ i, ∃ j, (i, j) = a := ⟨a.1, a.2, rfl⟩
  rcases lt_trichotomy a.1 a.2 with h | h | h
  · exact Or.inr ⟨hall, h⟩
  · exact Or.inl (Or.inr ⟨hall, h⟩)
  · exact Or.inl (Or.inl ⟨hall, h⟩)

theorem nodup_letters : (letters n).Nodup := by
  have hall : ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => (List.nodup_finRange n).map fun j j' h => by simpa using h, ?_⟩
    refine (List.nodup_finRange n).pairwise_of_forall_ne ?_
    intro i _ i' _ hii'
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨j, rfl⟩ ⟨j', h⟩
    exact hii' (congrArg Prod.fst h).symm
  simp only [letters]
  refine List.Nodup.append (List.Nodup.append (hall.filter _) (hall.filter _) ?_) (hall.filter _) ?_
  · simp only [List.disjoint_left, List.mem_filter, decide_eq_true_eq]
    rintro a ⟨_, h⟩ ⟨_, h'⟩
    exact absurd h (by rw [h']; exact lt_irrefl _)
  · simp only [List.disjoint_left, List.mem_append, List.mem_filter, decide_eq_true_eq]
    rintro a (⟨_, h⟩ | ⟨_, h⟩) ⟨_, h'⟩
    · exact lt_asymm h h'
    · exact absurd h' (by rw [h]; exact lt_irrefl _)

def expand (m : Fin n × Fin n →₀ ℕ) : List (Fin n × Fin n) :=
  (letters n).flatMap fun a => List.replicate (m a) a

noncomputable def canon (m : Fin n × Fin n →₀ ℕ) : U n := word (expand m)

theorem word_flatMap_replicate (l : List (Fin n × Fin n)) (m : Fin n × Fin n → ℕ) :
    word (l.flatMap fun a => List.replicate (m a) a) = (l.map fun a => e a ^ m a).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, word_append, ih, List.map_cons, List.prod_cons]
    congr 1
    simp [word, List.map_replicate, List.prod_replicate]

theorem canon_eq_prod (m : Fin n × Fin n →₀ ℕ) :
    canon m = ((letters n).map fun a => e a ^ m a).prod :=
  word_flatMap_replicate _ _

theorem count_expand (m : Fin n × Fin n →₀ ℕ) (a : Fin n × Fin n) :
    Multiset.count a ((expand m : List _) : Multiset _) = m a := by
  have key : ∀ l : List (Fin n × Fin n), l.Nodup →
      Multiset.count a ((l.flatMap fun b => List.replicate (m b) b : List _) : Multiset _) =
        if a ∈ l then m a else 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.flatMap_cons, ← Multiset.coe_add, Multiset.count_add, ih (List.nodup_cons.1 hl).2,
        Multiset.coe_replicate, Multiset.count_replicate]
      by_cases hb : b = a
      · subst hb; simp [(List.nodup_cons.1 hl).1]
      · simp [hb, Ne.symm hb]
  rw [expand, key _ nodup_letters, if_pos (mem_letters a)]

theorem toFinsupp_expand (m : Fin n × Fin n →₀ ℕ) :
    Multiset.toFinsupp ((expand m : List _) : Multiset _) = m := by
  ext a
  rw [Multiset.toFinsupp_apply, count_expand]

theorem perm_expand (w : List (Fin n × Fin n)) :
    w.Perm (expand (Multiset.toFinsupp (w : Multiset _))) := by
  refine Multiset.coe_eq_coe.1 ?_
  ext a
  rw [count_expand, Multiset.toFinsupp_apply]

theorem length_expand (m : Fin n × Fin n →₀ ℕ) : (expand m).length = m.degree := by
  rw [Finsupp.degree_eq_sum, expand, List.length_flatMap]
  simp only [List.length_replicate]
  have : (letters n).toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun a => List.mem_toFinset.2 (mem_letters a)
  rw [← this, List.sum_toFinset _ nodup_letters]

theorem degree_toFinsupp (w : List (Fin n × Fin n)) :
    Finsupp.degree (Multiset.toFinsupp (w : Multiset (Fin n × Fin n))) = w.length := by
  rw [← length_expand]
  exact (perm_expand w).length_eq.symm

theorem mem_of_mem_support_toFinsupp {w : List (Fin n × Fin n)} {a : Fin n × Fin n}
    (ha : a ∈ (Multiset.toFinsupp (w : Multiset _)).support) : a ∈ w := by
  rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at ha
  exact Multiset.mem_coe.1 ha

theorem mem_support_of_mem_expand {m : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n}
    (ha : a ∈ expand m) : a ∈ m.support := by
  rw [Finsupp.mem_support_iff, ← count_expand]
  exact (Multiset.count_pos.2 (Multiset.mem_coe.2 ha)).ne'
@[simp] theorem expand_zero : expand (0 : Fin n × Fin n →₀ ℕ) = [] := by
  simp [expand]

@[simp] theorem canon_zero : canon (0 : Fin n × Fin n →₀ ℕ) = 1 := by
  simp [canon]

def canonSpan (P : Fin n × Fin n → Prop) (lo hi : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ m : Fin n × Fin n →₀ ℕ, (∀ a ∈ m.support, P a) ∧ lo ≤ m.degree ∧
    m.degree ≤ hi ∧ canon m = u}

theorem canonSpan_mono {P : Fin n × Fin n → Prop} {lo lo' hi hi' : ℕ} (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : canonSpan P lo hi ≤ canonSpan P lo' hi' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨m, hm, h1, h2, rfl⟩
  exact ⟨m, hm, hlo.trans h1, h2.trans hhi, rfl⟩

theorem canon_mem_canonSpan {P : Fin n × Fin n → Prop} {m : Fin n × Fin n →₀ ℕ}
    (hm : ∀ a ∈ m.support, P a) : canon m ∈ canonSpan P m.degree m.degree :=
  Submodule.subset_span ⟨m, hm, le_rfl, le_rfl, rfl⟩

theorem word_mem_canonSpan {P : Fin n × Fin n → Prop} (hP : Closed P) :
    ∀ (w : List (Fin n × Fin n)), (∀ a ∈ w, P a) →
      word w ∈ canonSpan P (min 1 w.length) w.length := by
  intro w
  induction hk : w.length using Nat.strong_induction_on generalizing w with
  | _ k ih =>
  intro hw
  set m := Multiset.toFinsupp (w : Multiset (Fin n × Fin n))
  have hmP : ∀ a ∈ m.support, P a := fun a ha => hw a (mem_of_mem_support_toFinsupp ha)
  have hmdeg : m.degree = k := by rw [degree_toFinsupp, hk]
  have hcanon : canon m ∈ canonSpan P (min 1 k) k := by
    have := canon_mem_canonSpan hmP
    rw [hmdeg] at this
    exact canonSpan_mono (min_le_right _ _) le_rfl this
  rw [← sub_add_cancel (word w) (canon m)]
  refine Submodule.add_mem _ ?_ hcanon
  have hperm := word_sub_word_mem_of_perm hP (perm_expand w) hw
  rw [hk] at hperm
  change word w - word (expand m) ∈ _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  ·
    have hw' : w = expand m := by
      rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩
      · simp [m]
      · have h := perm_expand [a]
        exact (List.perm_singleton.1 h.symm).symm
      · simp at hk; omega
    rw [← hw', sub_self]
    exact Submodule.zero_mem _
  · refine (Submodule.span_le.2 ?_) hperm
    rintro _ ⟨v, hv, hvl, rfl⟩
    have := ih (k - 1) (by omega) v hvl hv
    rw [show min 1 (k - 1) = 1 by omega] at this
    exact canonSpan_mono (by omega) (by omega) this

theorem span_canon_eq_top : Submodule.span ℂ (Set.range (canon (n := n))) = ⊤ := by
  have hword : ∀ w : List (Fin n × Fin n), word w ∈ Submodule.span ℂ (Set.range (canon (n := n))) := by
    intro w
    have := word_mem_canonSpan closed_true w (fun _ _ => trivial)
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨m, -, -, -, rfl⟩
    exact Submodule.subset_span ⟨m, rfl⟩
  set S := Submodule.span ℂ (Set.range (canon (n := n)))
  have hS : Submodule.span ℂ (Set.range (word (n := n))) ≤ S :=
    Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact hword w)
  have hall : ∀ u : U n, u ∈ Submodule.span ℂ (Set.range (word (n := n))) := by
    intro u
    induction u using U.induction with
    | halg r =>
      rw [Algebra.algebraMap_eq_smul_one, ← word_nil]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
    | hι X =>
      rw [ι_eq_sum_e]
      refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
      rw [← word_singleton]
      exact Submodule.subset_span ⟨[a], rfl⟩
    | hmul a b ha hb =>
      have : Submodule.span ℂ (Set.range (word (n := n))) *
          Submodule.span ℂ (Set.range (word (n := n))) ≤
            Submodule.span ℂ (Set.range (word (n := n))) := by
        rw [Submodule.span_mul_span]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
        exact Submodule.subset_span ⟨v ++ w, word_append v w⟩
      exact this (Submodule.mul_mem_mul ha hb)
    | hadd a b ha hb => exact Submodule.add_mem _ ha hb
  exact eq_top_iff.2 fun u _ => hS (hall u)

def filt (d : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {u | ∃ w : List (Fin n × Fin n), w.length ≤ d ∧ word w = u}

theorem word_mem_filt {w : List (Fin n × Fin n)} {d : ℕ} (h : w.length ≤ d) : word w ∈ filt (n := n) d :=
  Submodule.subset_span ⟨w, h, rfl⟩

theorem filt_mono {d d' : ℕ} (h : d ≤ d') : filt (n := n) d ≤ filt d' :=
  Submodule.span_mono fun _ ⟨w, hw, hu⟩ => ⟨w, hw.trans h, hu⟩

theorem canon_mem_filt (m : Fin n × Fin n →₀ ℕ) : canon m ∈ filt (n := n) m.degree :=
  word_mem_filt (length_expand m).le

theorem wordSpan_le_filt (P : Fin n × Fin n → Prop) (k : ℕ) : wordSpan (n := n) P k ≤ filt k :=
  Submodule.span_le.2 fun _ ⟨w, _, hw, hu⟩ => Submodule.subset_span ⟨w, hw.le, hu⟩

theorem filt_le_canonSpan (d : ℕ) : filt (n := n) d ≤ canonSpan (fun _ => True) 0 d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, hw, rfl⟩
  exact canonSpan_mono (Nat.zero_le _) hw (word_mem_canonSpan closed_true w fun _ _ => trivial)

theorem word_sub_canon_mem_filt (w : List (Fin n × Fin n)) :
    word w - canon (Multiset.toFinsupp (w : Multiset _)) ∈ filt (n := n) (w.length - 1) :=
  wordSpan_le_filt _ _ (word_sub_word_mem_of_perm closed_true (perm_expand w) fun _ _ => trivial)

def rootAt (a : Fin n × Fin n) (k : Fin n) : ℤ :=
  (if k = a.1 then 1 else 0) - (if k = a.2 then 1 else 0)

def wt (m : Fin n × Fin n →₀ ℕ) (k : Fin n) : ℤ := m.sum fun a c => (c : ℤ) * rootAt a k

theorem e_diag_mul_sub (k : Fin n) (a : Fin n × Fin n) :
    e (k, k) * e a - e a * e (k, k) = (rootAt a k : ℂ) • e a := by
  rw [e_mul_sub_mul]
  obtain ⟨i, j⟩ := a
  simp only [rootAt]
  by_cases hi : k = i <;> by_cases hj : k = j
  · subst hi; subst hj; simp
  · subst hi; simp [hj, Ne.symm hj]
  · subst hj; simp [hi]
  · simp [hi, hj, Ne.symm hj]

theorem e_diag_mul_word_sub (k : Fin n) (w : List (Fin n × Fin n)) :
    e (k, k) * word w - word w * e (k, k) = (((w.map fun a => rootAt a k).sum : ℤ) : ℂ) • word w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [word_cons, List.map_cons, List.sum_cons]
    have h1 := e_diag_mul_sub k a
    calc e (k, k) * (e a * word w) - e a * word w * e (k, k)
        = (e (k, k) * e a - e a * e (k, k)) * word w + e a * (e (k, k) * word w - word w * e (k, k)) := by
          noncomm_ring
      _ = _ := by
          rw [h1, ih, smul_mul_assoc, mul_smul_comm, ← add_smul]
          push_cast; ring_nf

theorem sum_rootAt_expand (m : Fin n × Fin n →₀ ℕ) (k : Fin n) :
    ((expand m).map fun a => rootAt a k).sum = wt m k := by
  have hw : ∀ w : List (Fin n × Fin n), (w.map fun a => rootAt a k).sum =
      wt (Multiset.toFinsupp (w : Multiset _)) k := by
    intro w
    induction w with
    | nil => simp [wt]
    | cons a w ih =>
      rw [List.map_cons, List.sum_cons, ih,
        show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset _) by simp,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, wt, wt,
        Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring),
        Finsupp.sum_single_index (by simp)]
      push_cast; ring
  rw [hw, toFinsupp_expand]

theorem e_diag_mul_canon_sub (k : Fin n) (m : Fin n × Fin n →₀ ℕ) :
    e (k, k) * canon m - canon m * e (k, k) = (wt m k : ℂ) • canon m := by
  rw [canon, e_diag_mul_word_sub, sum_rootAt_expand]

end GroundTheory.Automorphic.HarishChandra
