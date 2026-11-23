import Mathlib

namespace GlobalTheory

namespace Shuffle

variable {A : Type}

noncomputable def shuffle : List A → List A → Multiset (List A)
  | [], v => {v}
  | a :: u, [] => {a :: u}
  | a :: u, b :: v =>
      (shuffle u (b :: v)).map (List.cons a) + (shuffle (a :: u) v).map (List.cons b)

@[simp] theorem shuffle_nil_left (v : List A) : shuffle [] v = {v} := by
  rw [shuffle]

@[simp] theorem shuffle_nil_right (u : List A) : shuffle u [] = {u} := by
  cases u <;> rw [shuffle]

theorem shuffle_cons_cons (a b : A) (u v : List A) :
    shuffle (a :: u) (b :: v) =
      (shuffle u (b :: v)).map (List.cons a) + (shuffle (a :: u) v).map (List.cons b) := by
  rw [shuffle]

theorem shuffle_comm : ∀ u v : List A, shuffle u v = shuffle v u
  | [], v => by simp
  | a :: u, [] => by simp
  | a :: u, b :: v => by
      rw [shuffle_cons_cons, shuffle_cons_cons, shuffle_comm u (b :: v), shuffle_comm (a :: u) v,
        add_comm]

theorem perm_of_mem_shuffle : ∀ (u v w : List A), w ∈ shuffle u v → w.Perm (u ++ v)
  | [], v, w, h => by simp at h; simp [h]
  | a :: u, [], w, h => by simp at h; simp [h]
  | a :: u, b :: v, w, h => by
      rw [shuffle_cons_cons, Multiset.mem_add, Multiset.mem_map, Multiset.mem_map] at h
      rcases h with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · exact (perm_of_mem_shuffle u (b :: v) x hx).cons a
      · exact ((perm_of_mem_shuffle (a :: u) v x hx).cons b).trans List.perm_middle.symm

theorem append_mem_shuffle : ∀ (u v : List A), u ++ v ∈ shuffle u v
  | [], v => by simp
  | a :: u, [] => by simp
  | a :: u, b :: v => by
      rw [shuffle_cons_cons, Multiset.mem_add]
      exact Or.inl (Multiset.mem_map.2 ⟨_, append_mem_shuffle u (b :: v), rfl⟩)

theorem bind_singleton_self (s : Multiset (List A)) : s.bind (fun x => {x}) = s := by
  simpa using Multiset.bind_singleton s id

theorem shuffle_assoc : ∀ u v w : List A,
    (shuffle u v).bind (fun x => shuffle x w) = (shuffle v w).bind (fun x => shuffle u x)
  | [], v, w => by simp [bind_singleton_self]
  | a :: u, [], w => by simp
  | a :: u, b :: v, [] => by simp [bind_singleton_self]
  | a :: u, b :: v, c :: w => by
      have h1 := shuffle_assoc u (b :: v) (c :: w)
      have h2 := shuffle_assoc (a :: u) v (c :: w)
      have h3 := shuffle_assoc (a :: u) (b :: v) w
      have e1 : (shuffle (a :: u) (b :: v)).bind (fun x => shuffle x (c :: w)) =
          ((shuffle u (b :: v)).bind (fun x => shuffle x (c :: w))).map (List.cons a) +
          ((shuffle (a :: u) v).bind (fun x => shuffle x (c :: w))).map (List.cons b) +
          ((shuffle (a :: u) (b :: v)).bind (fun x => shuffle x w)).map (List.cons c) := by
        simp only [shuffle_cons_cons a b, Multiset.add_bind, Multiset.bind_map,
          shuffle_cons_cons _ c, Multiset.bind_add, Multiset.map_bind, Multiset.map_add]
        abel
      have e2 : (shuffle (b :: v) (c :: w)).bind (fun x => shuffle (a :: u) x) =
          ((shuffle (b :: v) (c :: w)).bind (fun x => shuffle u x)).map (List.cons a) +
          ((shuffle v (c :: w)).bind (fun x => shuffle (a :: u) x)).map (List.cons b) +
          ((shuffle (b :: v) w).bind (fun x => shuffle (a :: u) x)).map (List.cons c) := by
        simp only [shuffle_cons_cons b c, Multiset.add_bind, Multiset.bind_map,
          shuffle_cons_cons a, Multiset.bind_add, Multiset.map_bind, Multiset.map_add]
        abel
      rw [e1, e2, h1, h2, h3]
termination_by u v w => u.length + v.length + w.length

end Shuffle

open Shuffle

def ShuffleAlgebra (K A : Type) [CommRing K] : Type := List A →₀ K

namespace ShuffleAlgebra

variable (K : Type) [CommRing K] {A : Type}

noncomputable instance : AddCommGroup (ShuffleAlgebra K A) :=
  inferInstanceAs (AddCommGroup (List A →₀ K))

noncomputable instance : Module K (ShuffleAlgebra K A) :=
  inferInstanceAs (Module K (List A →₀ K))

noncomputable def wordBasis (A : Type) : Module.Basis (List A) K (ShuffleAlgebra K A) :=
  (Finsupp.basisSingleOne : Module.Basis (List A) K (List A →₀ K))

noncomputable def word (w : List A) : ShuffleAlgebra K A := wordBasis K A w

theorem wordBasis_apply (w : List A) : wordBasis K A w = word K w := rfl

noncomputable def mulLin : ShuffleAlgebra K A →ₗ[K] ShuffleAlgebra K A →ₗ[K] ShuffleAlgebra K A :=
  (wordBasis K A).constr K fun u => (wordBasis K A).constr K fun v =>
    ((shuffle u v).map (word K)).sum

theorem mulLin_word (u v : List A) :
    mulLin K (word K u) (word K v) = ((shuffle u v).map (word K)).sum := by
  simp only [mulLin, ← wordBasis_apply, Module.Basis.constr_basis]

theorem mulLin_comm (x y : ShuffleAlgebra K A) : mulLin K x y = mulLin K y x := by
  have : mulLin K (A := A) = (mulLin K).flip := by
    refine (wordBasis K A).ext fun u => (wordBasis K A).ext fun v => ?_
    simp only [wordBasis_apply, LinearMap.flip_apply, mulLin_word, shuffle_comm u v]
  conv_lhs => rw [this]
  rfl

theorem mulLin_one (x : ShuffleAlgebra K A) : mulLin K (word K []) x = x := by
  have : mulLin K (word K ([] : List A)) = LinearMap.id := by
    refine (wordBasis K A).ext fun v => ?_
    simp [wordBasis_apply, mulLin_word]
  rw [this]; rfl

theorem mulLin_assoc (x y z : ShuffleAlgebra K A) :
    mulLin K (mulLin K x y) z = mulLin K x (mulLin K y z) := by
  have key : ∀ u v w : List A, mulLin K (mulLin K (word K u) (word K v)) (word K w) =
      mulLin K (word K u) (mulLin K (word K v) (word K w)) := by
    intro u v w
    have h := congrArg (fun s => (Multiset.map (word K) s).sum) (shuffle_assoc u v w)
    simp only [Multiset.map_bind, Multiset.sum_bind] at h
    rw [mulLin_comm, mulLin_word, mulLin_word, map_multiset_sum, map_multiset_sum,
      Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, mulLin_word, shuffle_comm w]
    exact h
  have h3 : ∀ u v : List A, mulLin K (mulLin K (word K u) (word K v)) =
      mulLin K (word K u) ∘ₗ mulLin K (word K v) := fun u v =>
    (wordBasis K A).ext fun w => key u v w
  have h2 : ∀ u : List A, ((mulLin K).flip z) ∘ₗ mulLin K (word K u) =
      mulLin K (word K u) ∘ₗ (mulLin K).flip z := fun u =>
    (wordBasis K A).ext fun v => LinearMap.congr_fun (h3 u v) z
  have h1 : ((mulLin K).flip z) ∘ₗ (mulLin K).flip y = (mulLin K).flip (mulLin K y z) :=
    (wordBasis K A).ext fun u => LinearMap.congr_fun (h2 u) y
  exact LinearMap.congr_fun h1 x

noncomputable instance : CommRing (ShuffleAlgebra K A) where
  __ := (inferInstance : AddCommGroup (ShuffleAlgebra K A))
  mul x y := mulLin K x y
  one := word K []
  left_distrib x y z := (mulLin K x).map_add y z
  right_distrib x y z := LinearMap.map_add₂ (mulLin K) x y z
  zero_mul x := LinearMap.map_zero₂ (mulLin K) x
  mul_zero x := (mulLin K x).map_zero
  mul_assoc := mulLin_assoc K
  one_mul := mulLin_one K
  mul_one x := (mulLin_comm K _ _).trans (mulLin_one K x)
  mul_comm := mulLin_comm K

theorem mul_def (x y : ShuffleAlgebra K A) : x * y = mulLin K x y := rfl

noncomputable instance : Algebra K (ShuffleAlgebra K A) :=
  Algebra.ofModule (fun r x y => LinearMap.map_smul₂ (mulLin K) r x y)
    (fun r x y => (mulLin K x).map_smul r y)

theorem word_nil : word K ([] : List A) = 1 := rfl

theorem word_mul_word (u v : List A) :
    word K u * word K v = ((shuffle u v).map (word K)).sum := mulLin_word K u v

instance [Nontrivial K] : Nontrivial (ShuffleAlgebra K A) :=
  inferInstanceAs (Nontrivial (List A →₀ K))

end ShuffleAlgebra

def IsLyndon {A : Type} [LinearOrder A] (w : List A) : Prop :=
  w ≠ [] ∧ ∀ u v : List A, u ≠ [] → v ≠ [] → w = u ++ v → List.Lex (· < ·) w v

theorem isLyndon_of_pairwise_lt {A : Type} [LinearOrder A] {w : List A} (hw : w ≠ [])
    (h : w.Pairwise (· < ·)) : IsLyndon w := by
  refine ⟨hw, fun u v hu hv e => ?_⟩
  subst e
  obtain ⟨a, u, rfl⟩ := List.exists_cons_of_ne_nil hu
  obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hv
  exact List.Lex.rel ((List.pairwise_cons.1 h).1 b (by simp))

namespace Lyndon

variable {A : Type} [LinearOrder A]

theorem lt_of_isLyndon {w : List A} (h : IsLyndon w) {u v : List A} (hu : u ≠ []) (hv : v ≠ [])
    (e : w = u ++ v) : w < v := h.2 u v hu hv e

theorem lt_cases {u v : List A} (h : u < v) :
    (∀ x y, u ++ x < v ++ y) ∨ ∃ t, t ≠ [] ∧ v = u ++ t := by
  have h' : List.Lex (· < ·) u v := h
  clear h
  induction h' with
  | nil => exact Or.inr ⟨_, by simp, rfl⟩
  | rel h => exact Or.inl fun x y => List.Lex.rel h
  | cons _ ih =>
    rcases ih with ih | ⟨t, ht, rfl⟩
    · exact Or.inl fun x y => List.Lex.cons (ih x y)
    · exact Or.inr ⟨t, ht, rfl⟩

theorem append_lt_of_lt_of_length {u v : List A} (h : u < v) (hl : v.length ≤ u.length)
    (x y : List A) : u ++ x < v ++ y := by
  rcases lt_cases h with h | ⟨t, ht, rfl⟩
  · exact h x y
  · exact absurd (by simpa using hl) ht

theorem append_lt_append_left (p : List A) {u v : List A} (h : u < v) : p ++ u < p ++ v := by
  induction p with
  | nil => exact h
  | cons a p ih => exact List.Lex.cons ih

theorem nil_le (u : List A) : [] ≤ u := by
  cases u with
  | nil => exact le_rfl
  | cons a u => exact le_of_lt (List.Lex.nil)

theorem le_append (p u : List A) : p ≤ p ++ u := by
  rcases (nil_le u).lt_or_eq with h | h
  · simpa using (append_lt_append_left p h).le
  · simp [← h]

theorem isLyndon_singleton (a : A) : IsLyndon [a] :=
  isLyndon_of_pairwise_lt (by simp) (by simp)

theorem isLyndon_append {l m : List A} (hl : IsLyndon l) (hm : IsLyndon m) (h : l < m) :
    IsLyndon (l ++ m) := by
  have h0 : l ++ m < m := by
    rcases lt_cases h with h | ⟨t, ht, e⟩
    · simpa using h m []
    · have := append_lt_append_left l (lt_of_isLyndon hm hl.1 ht e)
      rwa [← e] at this
  refine ⟨by simp [hl.1], fun u v hu hv e => ?_⟩
  change l ++ m < v
  rcases List.append_eq_append_iff.1 e with ⟨s, e1, e2⟩ | ⟨s, e1, e2⟩
  · by_cases hs : s = []
    · subst hs; simp at e2; rw [← e2]; exact h0
    · exact h0.trans (lt_of_isLyndon hm hs hv e2)
  · by_cases hs : s = []
    · subst hs; simp at e2; rw [e2]; exact h0
    · rw [e2]
      exact append_lt_of_lt_of_length (lt_of_isLyndon hl hu hs e1) (by simp [e1]) _ _

def IsFactors (L : List (List A)) : Prop := (∀ l ∈ L, IsLyndon l) ∧ L.Pairwise (· ≥ ·)

theorem IsFactors.tail {l : List A} {L : List (List A)} (h : IsFactors (l :: L)) : IsFactors L :=
  ⟨fun x hx => h.1 x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.1 h.2).2⟩

theorem exists_factors_cons (L : List (List A)) (hL : IsFactors L) :
    ∀ l, IsLyndon l → ∃ L', IsFactors L' ∧ L'.flatten = l ++ L.flatten := by
  induction L with
  | nil => exact fun l hl => ⟨[l], ⟨by simpa using hl, by simp⟩, by simp⟩
  | cons m L ih =>
    intro l hl
    rcases le_or_gt m l with h | h
    · refine ⟨l :: m :: L, ⟨?_, List.pairwise_cons.2 ⟨?_, hL.2⟩⟩, by simp⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hl
        · exact hL.1 x hx
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h
        · exact le_trans ((List.pairwise_cons.1 hL.2).1 x hx) h
    · obtain ⟨L', h1, h2⟩ := ih hL.tail (l ++ m) (isLyndon_append hl (hL.1 m (by simp)) h)
      exact ⟨L', h1, by simp [h2]⟩

theorem exists_factors (w : List A) : ∃ L, IsFactors L ∧ L.flatten = w := by
  induction w with
  | nil => exact ⟨[], ⟨by simp, by simp⟩, rfl⟩
  | cons a w ih =>
    obtain ⟨L, h1, h2⟩ := ih
    obtain ⟨L', h3, h4⟩ := exists_factors_cons L h1 [a] (isLyndon_singleton a)
    exact ⟨L', h3, by simp [h4, h2]⟩

theorem exists_suffix_le (l : List A) (L : List (List A)) (hL : ∀ m ∈ L, m ≤ l) :
    ∀ t r : List A, t ≠ [] → t ++ r = L.flatten → ∃ s q, q ≠ [] ∧ t = s ++ q ∧ q ≤ l := by
  induction L with
  | nil => intro t r ht e; simp [ht] at e
  | cons m L ih =>
    intro t r ht e
    rw [List.flatten_cons] at e
    have hm := hL m (by simp)
    rcases List.append_eq_append_iff.1 e with ⟨s, e1, e2⟩ | ⟨s, e1, e2⟩
    · exact ⟨[], t, ht, rfl, le_trans (e1 ▸ le_append t s) hm⟩
    · by_cases hs : s = []
      · subst hs; simp at e1; exact ⟨[], t, ht, rfl, e1 ▸ hm⟩
      · obtain ⟨s', q, h1, h2, h3⟩ :=
          ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) s r hs e2.symm
        exact ⟨m ++ s', q, h1, by simp [e1, h2], h3⟩

theorem eq_nil_of_head_append {l t r : List A} {L : List (List A)} (hL : IsFactors (l :: L))
    (hp : IsLyndon (l ++ t)) (e : L.flatten = t ++ r) : t = [] := by
  by_contra ht
  obtain ⟨s, q, h1, h2, h3⟩ :=
    exists_suffix_le l L (List.pairwise_cons.1 hL.2).1 t r ht e.symm
  have h4 : l ++ t < q :=
    lt_of_isLyndon hp (u := l ++ s) (by simp [(hL.1 l (by simp)).1]) h1 (by simp [h2])
  exact absurd (h4.trans_le (h3.trans (le_append l t))) (lt_irrefl _)

theorem factors_unique (L : List (List A)) (hL : IsFactors L) :
    ∀ L', IsFactors L' → L.flatten = L'.flatten → L = L' := by
  induction L with
  | nil =>
    intro L' h e
    cases L' with
    | nil => rfl
    | cons m L' => simp [(h.1 m (by simp)).1] at e
  | cons l L ih =>
    intro L' h e
    cases L' with
    | nil => simp [(hL.1 l (by simp)).1] at e
    | cons m L' =>
      simp only [List.flatten_cons] at e
      have : l = m := by
        rcases List.append_eq_append_iff.1 e with ⟨s, e1, e2⟩ | ⟨s, e1, e2⟩
        · have := eq_nil_of_head_append hL (e1 ▸ h.1 m (by simp)) e2
          simp [e1, this]
        · have := eq_nil_of_head_append h (e1 ▸ hL.1 l (by simp)) e2
          simp [e1, this]
      subst this
      rw [ih hL.tail L' h.tail (List.append_cancel_left e)]

noncomputable def Interleaves : List A → Multiset (List A) → Prop
  | [], S => ∀ u ∈ S, u = []
  | a :: w, S => ∃ u T, S = (a :: u) ::ₘ T ∧ Interleaves w (u ::ₘ T)

omit [LinearOrder A] in
theorem interleaves_nil_cons (w : List A) :
    ∀ S : Multiset (List A), Interleaves w ([] ::ₘ S) ↔ Interleaves w S := by
  induction w with
  | nil => intro S; simp [Interleaves]
  | cons a w ih =>
    intro S
    constructor
    · rintro ⟨u, T, e, h⟩
      rcases Multiset.cons_eq_cons.1 e with ⟨e1, _⟩ | ⟨_, R, e1, e2⟩
      · simp at e1
      · subst e1 e2
        rw [Multiset.cons_swap, ih] at h
        exact ⟨u, R, rfl, h⟩
    · rintro ⟨u, T, rfl, h⟩
      refine ⟨u, [] ::ₘ T, Multiset.cons_swap _ _ _, ?_⟩
      rw [Multiset.cons_swap, ih]; exact h

omit [LinearOrder A] in
theorem interleaves_of_mem_shuffle : ∀ (u x w : List A) (S : Multiset (List A)),
    w ∈ shuffle u x → Interleaves x S → Interleaves w (u ::ₘ S)
  | [], x, w, S, h, hS => by
      simp at h; subst h; exact (interleaves_nil_cons _ _).2 hS
  | a :: u, [], w, S, h, hS => by
      simp at h; subst h
      exact ⟨u, S, rfl, interleaves_of_mem_shuffle u [] u S (by simp) hS⟩
  | a :: u, b :: v, w, S, h, hS => by
      rw [shuffle_cons_cons, Multiset.mem_add, Multiset.mem_map, Multiset.mem_map] at h
      rcases h with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · exact ⟨u, S, rfl, interleaves_of_mem_shuffle u (b :: v) y S hy hS⟩
      · obtain ⟨t, T, rfl, hT⟩ := hS
        refine ⟨t, (a :: u) ::ₘ T, Multiset.cons_swap _ _ _, ?_⟩
        rw [Multiset.cons_swap]
        exact interleaves_of_mem_shuffle (a :: u) v y _ hy hT
termination_by u x => u.length + x.length

omit [LinearOrder A] in
theorem interleaves_split (w : List A) : ∀ (x y : List A) (S : Multiset (List A)),
    Interleaves w ((x ++ y) ::ₘ S) → Interleaves w (x ::ₘ y ::ₘ S) := by
  induction w with
  | nil => intro x y S h; simp [Interleaves] at h ⊢; tauto
  | cons a w ih =>
    rintro x y S ⟨u, T, e, h⟩
    rcases Multiset.cons_eq_cons.1 e with ⟨e1, e2⟩ | ⟨_, R, e1, e2⟩
    · subst e2
      cases x with
      | nil =>
        simp at e1; subst e1
        rw [interleaves_nil_cons]; exact ⟨u, S, rfl, h⟩
      | cons b x =>
        simp at e1
        obtain ⟨rfl, rfl⟩ := e1
        exact ⟨x, _, rfl, ih _ _ _ h⟩
    · subst e1 e2
      rw [Multiset.cons_swap] at h
      refine ⟨u, x ::ₘ y ::ₘ R, ?_, ?_⟩
      · rw [Multiset.cons_swap y, Multiset.cons_swap x]
      · rw [Multiset.cons_swap u, Multiset.cons_swap u]; exact ih _ _ _ h

omit [LinearOrder A] in
theorem interleaves_flatten (w : List A) (F : List (List A)) : ∀ S : Multiset (List A),
    Interleaves w (F.flatten ::ₘ S) → Interleaves w (↑F + S) := by
  induction F with
  | nil => intro S h; simpa [interleaves_nil_cons] using h
  | cons f F ih =>
    intro S h
    have h1 := interleaves_split w _ _ _ h
    rw [Multiset.cons_swap] at h1
    have h2 := ih _ h1
    rwa [Multiset.add_cons, ← Multiset.cons_add, Multiset.cons_coe] at h2

theorem exists_suffix_le_of_mem {F : List (List A)} (hF : IsFactors F) {f : List A} (hf : f ∈ F) :
    ∃ s g, g ≠ [] ∧ F.flatten = s ++ g ∧ g ≤ f := by
  rcases List.eq_nil_or_concat F with rfl | ⟨F', g, rfl⟩
  · simp at hf
  · rw [List.concat_eq_append] at hF hf ⊢
    refine ⟨F'.flatten, g, (hF.1 g (by simp)).1, by simp, ?_⟩
    rcases List.mem_append.1 hf with h | h
    · exact (List.pairwise_append.1 hF.2).2.2 f h g (by simp)
    · simp at h; exact h.ge

theorem exists_cut (m : List A) (F : List (List A)) (hF : F.Pairwise (· ≥ ·)) :
    ∃ P R, F = P ++ R ∧ (∀ f ∈ P, m ≤ f) ∧ ∀ f ∈ R, f ≤ m := by
  induction F with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons f F ih =>
    rcases le_total m f with h | h
    · obtain ⟨P, R, e, h1, h2⟩ := ih (List.pairwise_cons.1 hF).2
      refine ⟨f :: P, R, by simp [e], ?_, h2⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h
      · exact h1 x hx
    · refine ⟨[], f :: F, rfl, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h
      · exact le_trans ((List.pairwise_cons.1 hF).1 x hx) h

theorem exists_sorted (S : Multiset (List A)) :
    ∃ Q : List (List A), (Q : Multiset (List A)) = S ∧ Q.Pairwise (· ≥ ·) :=
  ⟨S.sort (· ≥ ·), Multiset.sort_eq _ _, Multiset.pairwise_sort _ _⟩

theorem exists_factors_step {L F : List (List A)} {a : A} {u : List A} {T : Multiset (List A)}
    (hL : IsFactors L) (hF : IsFactors F) (hu : F.flatten = u)
    (e : (L : Multiset (List A)) = (a :: u) ::ₘ T) :
    ∃ L', IsFactors L' ∧ (L' : Multiset (List A)) = ↑F + T ∧ a :: L'.flatten ≤ L.flatten := by
  cases L with
  | nil => exact absurd e.symm (Multiset.cons_ne_zero)
  | cons m L =>
    have hm := hL.1 m (by simp)
    have hmax := (List.pairwise_cons.1 hL.2).1
    rw [← Multiset.cons_coe] at e
    rcases Multiset.cons_eq_cons.1 e with ⟨e1, e2⟩ | ⟨hne, R, e1, e2⟩
    · subst e1 e2
      refine ⟨F ++ L, ⟨?_, List.pairwise_append.2 ⟨hF.2, hL.tail.2, ?_⟩⟩, by simp, by simp [hu]⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hF.1 x hx
        · exact hL.tail.1 x hx
      · intro f hf x hx
        obtain ⟨s, g, h1, h2, h3⟩ := exists_suffix_le_of_mem hF hf
        have : a :: u < g := lt_of_isLyndon hm (u := a :: s) (by simp) h1 (by simp [← hu, h2])
        exact le_trans (hmax x hx) (this.le.trans h3)
    · subst e2
      have hmem : ∀ x, x ∈ (a :: u) ::ₘ R → x ∈ L := fun x hx => by
        rw [← e1] at hx; exact Multiset.mem_coe.1 hx
      have hlt : a :: u < m :=
        lt_of_le_of_ne (hmax _ (hmem _ (Multiset.mem_cons_self _ _))) (Ne.symm hne)
      obtain ⟨P, P', eF, h1, h2⟩ := exists_cut m F hF.2
      obtain ⟨Q, hQ, hQs⟩ := exists_sorted ((P' : Multiset (List A)) + R)
      have hQm : ∀ x ∈ Q, x ∈ P' ∨ x ∈ L := fun x hx => by
        have : x ∈ (↑P' + R : Multiset (List A)) := by rw [← hQ]; exact Multiset.mem_coe.2 hx
        rcases Multiset.mem_add.1 this with h | h
        · exact Or.inl (Multiset.mem_coe.1 h)
        · exact Or.inr (hmem x (Multiset.mem_cons_of_mem h))
      have hQle : ∀ x ∈ Q, x ≤ m := fun x hx => (hQm x hx).elim (h2 x) (hmax x)
      subst eF
      refine ⟨P ++ m :: Q, ⟨?_, List.pairwise_append.2 ⟨(List.pairwise_append.1 hF.2).1,
        List.pairwise_cons.2 ⟨hQle, hQs⟩, ?_⟩⟩, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hF.1 x (List.mem_append_left _ hx)
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hm
          · exact (hQm x hx).elim (fun h => hF.1 x (List.mem_append_right _ h)) (hL.tail.1 x)
      · intro f hf x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1 f hf
        · exact le_trans (hQle x hx) (h1 f hf)
      · rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.cons_coe, hQ, Multiset.add_cons,
          Multiset.add_cons, add_assoc]
      · have hp : a :: P.flatten < m := by
          refine lt_of_le_of_lt ?_ hlt
          have := le_append (a :: P.flatten) P'.flatten
          simpa [← hu] using this
        have goal : (a :: P.flatten) ++ (m ++ Q.flatten) < m ++ L.flatten := by
          rcases lt_cases hp with h | ⟨q, hq, em⟩
          · exact h _ _
          · have h3 := append_lt_of_lt_of_length (lt_of_isLyndon hm (by simp) hq em)
              (by rw [em]; simp; omega) Q.flatten L.flatten
            have h4 := append_lt_append_left (a :: P.flatten) h3
            rwa [← List.append_assoc _ q, ← em] at h4
        simpa using goal.le

theorem le_flatten_of_interleaves (w : List A) : ∀ L : List (List A), IsFactors L →
    Interleaves w ↑L → w ≤ L.flatten := by
  induction w with
  | nil => exact fun L _ _ => nil_le _
  | cons a w ih =>
    rintro L hL ⟨u, T, e, h⟩
    obtain ⟨F, hF, hu⟩ := exists_factors u
    obtain ⟨L', h1, h2, h3⟩ := exists_factors_step hL hF hu e
    have h4 := interleaves_flatten w F T (hu ▸ h)
    rw [← h2] at h4
    refine le_trans ?_ h3
    rcases (ih L' h1 h4).lt_or_eq with h | h
    · exact (append_lt_append_left [a] h).le
    · rw [h]

noncomputable def shuffleList {A : Type} : List (List A) → Multiset (List A)
  | [] => {[]}
  | u :: L => (shuffleList L).bind (shuffle u)

omit [LinearOrder A] in
theorem flatten_mem_shuffleList (L : List (List A)) : L.flatten ∈ shuffleList L := by
  induction L with
  | nil => simp [shuffleList]
  | cons u L ih => exact Multiset.mem_bind.2 ⟨_, ih, append_mem_shuffle _ _⟩

omit [LinearOrder A] in
theorem of_mem_shuffleList (L : List (List A)) :
    ∀ w ∈ shuffleList L, w.Perm L.flatten ∧ Interleaves w ↑L := by
  induction L with
  | nil => intro w hw; simp [shuffleList] at hw; subst hw; simp [Interleaves]
  | cons u L ih =>
    intro w hw
    obtain ⟨x, hx, hw⟩ := Multiset.mem_bind.1 hw
    exact ⟨(perm_of_mem_shuffle _ _ _ hw).trans ((ih x hx).1.append_left u),
      interleaves_of_mem_shuffle u x w _ hw (ih x hx).2⟩

open ShuffleAlgebra

variable (K : Type) [Field K]

omit [LinearOrder A] in
theorem prod_word (L : List (List A)) :
    (L.map (word K)).prod = ((shuffleList L).map (word K)).sum := by
  induction L with
  | nil => simp [shuffleList, word_nil]
  | cons u L ih =>
    rw [List.map_cons, List.prod_cons, ih, ← Multiset.sum_map_mul_left, shuffleList,
      Multiset.map_bind, Multiset.sum_bind]
    simp only [word_mul_word]

theorem repr_sum_word (s : Multiset (List A)) (w : List A) :
    (wordBasis K A).repr (s.map (word K)).sum w = (s.count w : K) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, map_add, Finsupp.add_apply, ih,
      ← wordBasis_apply, Module.Basis.repr_self, Multiset.count_cons, Finsupp.single_apply]
    by_cases h : x = w
    · simp [h, add_comm]
    · simp [h, Ne.symm h]

theorem repr_prod_self [CharZero K] (L : List (List A)) :
    (wordBasis K A).repr (L.map (word K)).prod L.flatten ≠ 0 := by
  rw [prod_word, repr_sum_word, Nat.cast_ne_zero]
  exact Multiset.count_ne_zero.2 (flatten_mem_shuffleList L)

theorem le_of_repr_prod_ne_zero {L : List (List A)} (hL : IsFactors L) {w : List A}
    (h : (wordBasis K A).repr (L.map (word K)).prod w ≠ 0) :
    w.Perm L.flatten ∧ w ≤ L.flatten := by
  rw [prod_word, repr_sum_word] at h
  have hw : w ∈ shuffleList L := by
    by_contra hw
    exact h (by rw [Multiset.count_eq_zero.2 hw, Nat.cast_zero])
  exact ⟨(of_mem_shuffleList L w hw).1,
    le_flatten_of_interleaves w L hL (of_mem_shuffleList L w hw).2⟩

theorem word_mem_of_lyndon_mem [CharZero K] (B : Subalgebra K (ShuffleAlgebra K A))
    (hB : ∀ l, IsLyndon l → word K l ∈ B) (w : List A) : word K w ∈ B := by
  classical
  induction hn : (w.permutations.toFinset.filter (· < w)).card using Nat.strong_induction_on
    generalizing w with
  | _ n ih =>
    obtain ⟨L, hL, rfl⟩ := exists_factors w
    set x := (L.map (word K)).prod with hx
    have hxB : x ∈ B := B.list_prod_mem fun y hy => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
      exact hB l (hL.1 l hl)
    have hc := repr_prod_self K L
    rw [← hx] at hc
    have hsum : x = ∑ v ∈ ((wordBasis K A).repr x).support,
        (wordBasis K A).repr x v • word K v := by
      conv_lhs => rw [← (wordBasis K A).linearCombination_repr x]
      rfl
    rw [← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.2 hc)] at hsum
    have hrest : ∑ v ∈ ((wordBasis K A).repr x).support.erase L.flatten,
        (wordBasis K A).repr x v • word K v ∈ B := by
      refine B.sum_mem fun v hv => B.smul_mem ?_ _
      obtain ⟨hne, hv⟩ := Finset.mem_erase.1 hv
      obtain ⟨hp, hle⟩ := le_of_repr_prod_ne_zero K hL (Finsupp.mem_support_iff.1 hv)
      have hlt := lt_of_le_of_ne hle hne
      refine ih _ ?_ v rfl
      rw [← hn]
      refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, List.mem_toFinset, List.mem_permutations] at hy ⊢
        exact ⟨hy.1.trans hp, hy.2.trans hlt⟩
      · have := @hsub v (by
          simp only [Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
          exact ⟨hp, hlt⟩)
        simp at this
    have h1 : (wordBasis K A).repr x L.flatten • word K L.flatten ∈ B := by
      rw [eq_sub_iff_add_eq.2 hsum.symm]
      exact B.sub_mem hxB hrest
    have h2 := B.smul_mem h1 ((wordBasis K A).repr x L.flatten)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

theorem monomial_eq_prod {σ : Type} (d : σ →₀ ℕ) :
    (MvPolynomial.monomial d (1 : K)) = ((Finsupp.toMultiset d).map MvPolynomial.X).prod := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Multiset.map_add, Multiset.prod_add, ← hf, ← hg, MvPolynomial.monomial_mul,
      one_mul]
  | single a n =>
    rw [Finsupp.toMultiset_single, ← MvPolynomial.X_pow_eq_monomial]
    simp [Multiset.map_nsmul, Multiset.prod_nsmul]

theorem aeval_injective [CharZero K] : Function.Injective
    (MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => word K l.1) :
      MvPolynomial {w : List A // IsLyndon w} K →ₐ[K] ShuffleAlgebra K A) := by
  classical
  choose Λ hΛ hΛs using fun d : {w : List A // IsLyndon w} →₀ ℕ =>
    exists_sorted ((Finsupp.toMultiset d).map Subtype.val)
  have hfac : ∀ d, IsFactors (Λ d) := fun d => ⟨fun l hl => by
    have : l ∈ (Finsupp.toMultiset d).map Subtype.val := by
      rw [← hΛ]; exact Multiset.mem_coe.2 hl
    obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 this
    exact y.2, hΛs d⟩
  have hinj : ∀ d d', (Λ d).flatten = (Λ d').flatten → d = d' := fun d d' h => by
    have h1 := factors_unique _ (hfac d) _ (hfac d') h
    have h2 : (Finsupp.toMultiset d).map Subtype.val =
        (Finsupp.toMultiset d').map Subtype.val := by rw [← hΛ, ← hΛ, h1]
    exact Multiset.toFinsupp.symm.injective
      (Multiset.map_injective Subtype.val_injective h2)
  have hmon : ∀ d, MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => word K l.1)
      (MvPolynomial.monomial d (1 : K)) = ((Λ d).map (word K)).prod := fun d => by
    rw [monomial_eq_prod, map_multiset_prod, ← Multiset.prod_coe, ← Multiset.map_coe, hΛ,
      Multiset.map_map, Multiset.map_map]
    simp
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  obtain ⟨d₀, hd₀, hmax⟩ := p.support.exists_max_image (fun d => (Λ d).flatten)
    (MvPolynomial.support_nonempty.2 hne)
  have hsum : p = ∑ d ∈ p.support, p.coeff d • MvPolynomial.monomial d (1 : K) := by
    conv_lhs => rw [p.as_sum]
    simp [MvPolynomial.smul_monomial]
  rw [hsum, map_sum] at hp
  have h1 := congrArg (fun x => (wordBasis K A).repr x (Λ d₀).flatten) hp
  simp only [map_smul, hmon, map_sum, Finsupp.finsetSum_apply, Finsupp.smul_apply, map_zero,
    Finsupp.zero_apply, smul_eq_mul] at h1
  rw [Finset.sum_eq_single d₀] at h1
  · exact mul_ne_zero (MvPolynomial.mem_support_iff.1 hd₀) (repr_prod_self K _) h1
  · intro d hd hdne
    by_contra h
    have h2 := (le_of_repr_prod_ne_zero K (hfac d) (right_ne_zero_of_mul h)).2
    exact hdne (hinj _ _ (le_antisymm (hmax d hd) h2))
  · exact fun h => absurd hd₀ h

theorem aeval_surjective [CharZero K] : Function.Surjective
    (MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => word K l.1) :
      MvPolynomial {w : List A // IsLyndon w} K →ₐ[K] ShuffleAlgebra K A) := by
  intro x
  change x ∈ AlgHom.range _
  rw [← (wordBasis K A).linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Subalgebra.sum_mem _ fun v _ => Subalgebra.smul_mem _ ?_ _
  exact word_mem_of_lyndon_mem K _
    (fun l hl => (AlgHom.mem_range _).2 ⟨MvPolynomial.X ⟨l, hl⟩, MvPolynomial.aeval_X _ _⟩) v

end Lyndon

namespace Published

def RadfordShufflePolynomial : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : Type) [LinearOrder A],
    Function.Bijective
      (MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word K l.1) :
        MvPolynomial {w : List A // IsLyndon w} K →ₐ[K] ShuffleAlgebra K A)

theorem RadfordShufflePolynomial.algebraicIndependent (h : RadfordShufflePolynomial)
    (K : Type) [Field K] [CharZero K] (A : Type) [LinearOrder A] :
    AlgebraicIndependent K
      (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word K l.1) :=
  (h K A).1

theorem radfordShufflePolynomial_holds : RadfordShufflePolynomial :=
  fun K _ _ _ _ => ⟨Lyndon.aeval_injective K, Lyndon.aeval_surjective K⟩

end Published

end GlobalTheory
