import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ConstVanishHypSegment
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell faceSign)

namespace CechConstVanish

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
  {V : Type} [AddCommGroup V]

def pt (a : ∀ k, ι k) : Cell K ι 0 :=
  ⟨fun l => {a l}, fun _ => Finset.singleton_nonempty _, by simp⟩

def edge (a : ∀ k, ι k) (k : K) (u v : ι k) (h : u ≠ v) : Cell K ι 1 :=
  ⟨Function.update (fun l => ({a l} : Finset (ι l))) k {u, v}, by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k
      · subst hl; simp
      · simp [Function.update_of_ne hl]
    · rw [Finset.sum_eq_single k]
      · simp [Finset.card_pair h]
      · intro l _ hl; simp [Function.update_of_ne hl]
      · simp⟩

def tri (a : ∀ k, ι k) (k : K) (u v w : ι k) (huv : u < v) (hvw : v < w) : Cell K ι 2 :=
  ⟨Function.update (fun l => ({a l} : Finset (ι l))) k {u, v, w}, by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k
      · subst hl; simp
      · simp [Function.update_of_ne hl]
    · rw [Finset.sum_eq_single k]
      · rw [Function.update_self, Finset.card_insert_of_notMem (by simp [huv.ne, (huv.trans hvw).ne]),
          Finset.card_pair hvw.ne]
      · intro l _ hl; simp [Function.update_of_ne hl]
      · simp⟩

def sq (a : ∀ k, ι k) (k k' : K) (hk : k ≠ k') (u v : ι k) (u' v' : ι k') (h : u ≠ v) (h' : u' ≠ v') :
    Cell K ι 2 :=
  ⟨Function.update (Function.update (fun l => ({a l} : Finset (ι l))) k {u, v}) k' {u', v'}, by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k'
      · subst hl; simp
      · by_cases hl' : l = k
        · subst hl'; simp [Function.update_of_ne hl]
        · simp [Function.update_of_ne hl, Function.update_of_ne hl']
    · have e : ∀ l, ((Function.update (Function.update (fun l => ({a l} : Finset (ι l))) k {u, v}) k' {u', v'}
          l).card - 1) = (if l = k then 1 else 0) + (if l = k' then 1 else 0) := by
        intro l
        by_cases hl : l = k'
        · subst hl; simp [Finset.card_pair h', Ne.symm hk]
        · by_cases hl' : l = k
          · subst hl'; simp [Finset.card_pair h, hl]
          · simp [hl, hl']
      simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]⟩

theorem term_face {n : ℕ} (f : Cell K ι n → V) (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (T : Cell K ι n)
    (hT : Function.update I k ((I k).erase i) = T.1)
    [Decidable ((∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n)] :
    (if h : (∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n then
      faceSign I k i • f ⟨Function.update I k ((I k).erase i), h⟩ else 0) = faceSign I k i • f T := by
  have h : (∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n := by rw [hT]; exact T.2
  rw [dif_pos h]
  have e : (⟨Function.update I k ((I k).erase i), h⟩ : Cell K ι n) = T := Subtype.ext hT
  rw [e]

theorem term_single {n : ℕ} (f : Cell K ι n → V) (I : ∀ k, Finset (ι k)) (k : K) (i : ι k)
    (hI : I k = {i})
    [Decidable ((∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n)] :
    (if h : (∀ l, (Function.update I k ((I k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I k ((I k).erase i) l).card - 1) = n then
      faceSign I k i • f ⟨Function.update I k ((I k).erase i), h⟩ else 0) = 0 := by
  rw [dif_neg]
  intro h
  have := h.1 k
  rw [Function.update_self, hI] at this
  simp at this

theorem pt_update (a : ∀ k, ι k) (k : K) (x : ι k) :
    (pt (Function.update a k x)).1 = Function.update (fun l => ({a l} : Finset (ι l))) k {x} := by
  funext l
  by_cases hl : l = k
  · subst hl; simp [pt]
  · simp [pt, Function.update_of_ne hl]

theorem constD_edge (f : Cell K ι 0 → V) (a : ∀ k, ι k) (k : K) (u v : ι k) (h : u < v) :
    constD K ι V 0 f (edge a k u v h.ne) = f (pt (Function.update a k v)) - f (pt (Function.update a k u)) := by
  have hE : ∀ l, l ≠ k → (edge a k u v h.ne).1 l = {a l} := fun l hl => by simp [edge, Function.update_of_ne hl]
  have hEk : (edge a k u v h.ne).1 k = {u, v} := by simp [edge]
  have hpre : ∑ l ∈ Finset.univ.filter (· < k), (((edge a k u v h.ne).1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hE l (ne_of_lt (Finset.mem_filter.mp hl).2)]; simp
  simp only [constD]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_congr hEk (fun _ _ => rfl), Finset.sum_pair h.ne,
      term_face _ _ _ _ (pt (Function.update a k v)), term_face _ _ _ _ (pt (Function.update a k u))]
    · simp [faceSign, hpre, hEk, Finset.filter_insert, Finset.filter_singleton, h, not_lt_of_gt h]
      abel
    all_goals
      rw [pt_update, hEk]
      simp only [edge, Function.update_idem]
      congr 1
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      have := h.ne
      grind
  · intro l _ hl
    exact Finset.sum_eq_zero fun i hi => by
      rw [hE l hl, Finset.mem_singleton] at hi
      subst hi
      exact term_single _ _ _ _ (hE l hl)
  · simp

theorem constD_tri (z : Cell K ι 1 → V) (a : ∀ k, ι k) (k : K) (u v w : ι k) (huv : u < v) (hvw : v < w) :
    constD K ι V 1 z (tri a k u v w huv hvw) =
      z (edge a k v w hvw.ne) - z (edge a k u w (huv.trans hvw).ne) + z (edge a k u v huv.ne) := by
  have huw := huv.trans hvw
  have hE : ∀ l, l ≠ k → (tri a k u v w huv hvw).1 l = {a l} := fun l hl => by
    simp [tri, Function.update_of_ne hl]
  have hEk : (tri a k u v w huv hvw).1 k = {u, v, w} := by simp [tri]
  have hpre : ∑ l ∈ Finset.univ.filter (· < k), (((tri a k u v w huv hvw).1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hE l (ne_of_lt (Finset.mem_filter.mp hl).2)]; simp
  simp only [constD]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_congr hEk (fun _ _ => rfl), Finset.sum_insert (by simp [huv.ne, huw.ne]), Finset.sum_pair hvw.ne,
      term_face _ _ _ _ (edge a k v w hvw.ne), term_face _ _ _ _ (edge a k u w huw.ne),
      term_face _ _ _ _ (edge a k u v huv.ne)]
    · have h1 : ({u, v, w} : Finset (ι k)).filter (· < u) = ∅ := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; grind
      have h2 : ({u, v, w} : Finset (ι k)).filter (· < v) = {u} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; grind
      have h3 : ({u, v, w} : Finset (ι k)).filter (· < w) = {u, v} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; grind
      simp only [faceSign, hpre, hEk, h1, h2, h3, Finset.card_empty, Finset.card_singleton,
        Finset.card_pair huv.ne]
      simp
      abel
    all_goals
      rw [hEk]
      simp only [edge, tri, Function.update_idem]
      congr 1
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      grind
  · intro l _ hl
    exact Finset.sum_eq_zero fun i hi => by
      rw [hE l hl, Finset.mem_singleton] at hi
      subst hi
      exact term_single _ _ _ _ (hE l hl)
  · simp

theorem constD_sq (z : Cell K ι 1 → V) (a : ∀ k, ι k) (k k' : K) (hk : k < k') (u v : ι k) (u' v' : ι k')
    (h : u < v) (h' : u' < v') :
    constD K ι V 1 z (sq a k k' hk.ne u v u' v' h.ne h'.ne) =
      z (edge (Function.update a k v) k' u' v' h'.ne) - z (edge (Function.update a k u) k' u' v' h'.ne)
        - z (edge (Function.update a k' v') k u v h.ne) + z (edge (Function.update a k' u') k u v h.ne) := by
  have hE : ∀ l, l ≠ k → l ≠ k' → (sq a k k' hk.ne u v u' v' h.ne h'.ne).1 l = {a l} := fun l h1 h2 => by
    simp [sq, Function.update_of_ne h1, Function.update_of_ne h2]
  have hEk : (sq a k k' hk.ne u v u' v' h.ne h'.ne).1 k = {u, v} := by
    simp [sq, Function.update_of_ne hk.ne]
  have hEk' : (sq a k k' hk.ne u v u' v' h.ne h'.ne).1 k' = {u', v'} := by simp [sq]
  have hpre : ∑ l ∈ Finset.univ.filter (· < k), (((sq a k k' hk.ne u v u' v' h.ne h'.ne).1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      have hl' := (Finset.mem_filter.mp hl).2
      rw [hE l (ne_of_lt hl') (ne_of_lt (hl'.trans hk))]; simp
  have hpre' : ∑ l ∈ Finset.univ.filter (· < k'), (((sq a k k' hk.ne u v u' v' h.ne h'.ne).1 l).card - 1) = 1 := by
    rw [Finset.sum_eq_single k]
    · rw [hEk, Finset.card_pair h.ne]
    · intro l hl h1
      rw [hE l h1 (ne_of_lt (Finset.mem_filter.mp hl).2)]; simp
    · simp [hk]
  simp only [constD]
  rw [Finset.sum_eq_add_of_mem k k' (Finset.mem_univ _) (Finset.mem_univ _) hk.ne]
  · rw [Finset.sum_congr hEk (fun _ _ => rfl), Finset.sum_pair h.ne, Finset.sum_congr hEk' (fun _ _ => rfl),
      Finset.sum_pair h'.ne,
      term_face _ _ _ _ (edge (Function.update a k v) k' u' v' h'.ne),
      term_face _ _ _ _ (edge (Function.update a k u) k' u' v' h'.ne),
      term_face _ _ _ _ (edge (Function.update a k' v') k u v h.ne),
      term_face _ _ _ _ (edge (Function.update a k' u') k u v h.ne)]
    · simp [faceSign, hpre, hpre', hEk, hEk', Finset.filter_insert, Finset.filter_singleton, h, h',
        not_lt_of_gt h, not_lt_of_gt h']
      abel
    all_goals
      funext l
      rcases eq_or_ne l k with rfl | h1
      · simp only [sq, edge, Function.update_self, Function.update_of_ne hk.ne]
        try (ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; grind)
      rcases eq_or_ne l k' with rfl | h2
      · simp only [sq, edge, Function.update_self, Function.update_of_ne h1]
        try (ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; grind)
      · simp [sq, edge, Function.update_of_ne h1, Function.update_of_ne h2]
  · intro l _ hl
    exact Finset.sum_eq_zero fun i hi => by
      rw [hE l hl.1 hl.2, Finset.mem_singleton] at hi
      subst hi
      exact term_single _ _ _ _ (hE l hl.1 hl.2)

theorem tri_sub {G : ∀ k, Finset (ι k)} {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k : K} {u v w : ι k}
    (huv : u < v) (hvw : v < w) (hu : u ∈ G k) (hv : v ∈ G k) (hw : w ∈ G k) :
    ∀ l, (tri a k u v w huv hvw).1 l ⊆ G l := by
  intro l
  by_cases hl : l = k
  · subst hl; simp [tri, Finset.insert_subset_iff, hu, hv, hw]
  · simp [tri, Function.update_of_ne hl, ha l]

theorem sq_sub {G : ∀ k, Finset (ι k)} {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k k' : K} (hk : k ≠ k')
    {u v : ι k} {u' v' : ι k'} (h : u ≠ v) (h' : u' ≠ v') (hu : u ∈ G k) (hv : v ∈ G k) (hu' : u' ∈ G k')
    (hv' : v' ∈ G k') : ∀ l, (sq a k k' hk u v u' v' h h').1 l ⊆ G l := by
  intro l
  by_cases hl : l = k'
  · subst hl; simp [sq, Finset.insert_subset_iff, hu', hv']
  · by_cases hl' : l = k
    · subst hl'; simp [sq, Function.update_of_ne hl, Finset.insert_subset_iff, hu, hv]
    · simp [sq, Function.update_of_ne hl, Function.update_of_ne hl', ha l]

theorem edge_congr {a b : ∀ k, ι k} {k : K} {u v : ι k} (h : u ≠ v) (hab : ∀ l, l ≠ k → a l = b l) :
    edge a k u v h = edge b k u v h := by
  apply Subtype.ext
  funext l
  by_cases hl : l = k
  · subst hl; simp [edge]
  · simp [edge, Function.update_of_ne hl, hab l hl]

section Oriented

variable (z : Cell K ι 1 → V)

def oz (a : ∀ k, ι k) (k : K) (u v : ι k) : V :=
  if h : u < v then z (edge a k u v h.ne) else if h' : v < u then -z (edge a k v u h'.ne) else 0

theorem oz_of_lt {a : ∀ k, ι k} {k : K} {u v : ι k} (h : u < v) : oz z a k u v = z (edge a k u v h.ne) := by
  simp [oz, h]

theorem oz_self (a : ∀ k, ι k) (k : K) (u : ι k) : oz z a k u u = 0 := by
  simp [oz]

theorem oz_swap (a : ∀ k, ι k) (k : K) (u v : ι k) : oz z a k v u = -oz z a k u v := by
  rcases lt_trichotomy u v with h | rfl | h
  · simp [oz, h, not_lt_of_gt h]
  · simp [oz]
  · simp [oz, h, not_lt_of_gt h]

theorem oz_congr {a b : ∀ k, ι k} {k : K} (u v : ι k) (hab : ∀ l, l ≠ k → a l = b l) :
    oz z a k u v = oz z b k u v := by
  unfold oz
  split_ifs with h1 h2
  · rw [edge_congr _ hab]
  · rw [edge_congr _ hab]
  · rfl

variable {G : ∀ k, Finset (ι k)} (hz : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0)
include hz

theorem oz_tri {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k : K} {x u v : ι k} (hx : x ∈ G k) (hu : u ∈ G k)
    (hv : v ∈ G k) : oz z a k x v - oz z a k x u = oz z a k u v := by
  have hA : ∀ p q r : ι k, p ∈ G k → q ∈ G k → r ∈ G k → p < q → q < r →
      oz z a k p r = oz z a k p q + oz z a k q r := by
    intro p q r hp hq hr hpq hqr
    have e := hz _ (tri_sub ha hpq hqr hp hq hr)
    rw [constD_tri] at e
    rw [oz_of_lt z hpq, oz_of_lt z hqr, oz_of_lt z (hpq.trans hqr), ← sub_eq_zero, ← neg_eq_zero, ← e]
    abel
  by_cases e1 : x = u
  · subst e1; rw [oz_self, sub_zero]
  by_cases e2 : u = v
  · subst e2; rw [oz_self, sub_self]
  by_cases e3 : x = v
  · subst e3; rw [oz_self, zero_sub, oz_swap z a k u x, neg_neg]
  rw [sub_eq_iff_eq_add']
  have s1 := oz_swap z a k x u
  have s2 := oz_swap z a k u v
  have s3 := oz_swap z a k x v
  rcases lt_or_gt_of_ne e1 with h1 | h1 <;> rcases lt_or_gt_of_ne e2 with h2 | h2 <;>
    rcases lt_or_gt_of_ne e3 with h3 | h3
  all_goals first
    | exact absurd (h1.trans h2) (lt_asymm h3)
    | exact absurd (h2.trans h1) (lt_asymm h3)
    | exact hA x u v hx hu hv h1 h2
    | (first
        | have hh := hA u x v hu hx hv h1 h3
        | have hh := hA u v x hu hv hx h2 h3
        | have hh := hA x v u hx hv hu h3 h2
        | have hh := hA v x u hv hx hu h3 h1
        | have hh := hA v u x hv hu hx h2 h1
       simp only [s1, s2, s3] at hh ⊢
       first
        | (rw [← sub_eq_zero] at hh ⊢; rw [← hh]; abel1)
        | (rw [← sub_eq_zero] at hh ⊢; rw [← neg_eq_zero, ← hh]; abel1))

end Oriented

section Square

variable (z : Cell K ι 1 → V) {G : ∀ k, Finset (ι k)}
  (hz : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0)
include hz

theorem oz_sq_core {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k k' : K} (hk : k < k') {u v : ι k} {u' v' : ι k'}
    (h : u < v) (h' : u' < v') (hu : u ∈ G k) (hv : v ∈ G k) (hu' : u' ∈ G k') (hv' : v' ∈ G k') :
    oz z (Function.update a k v) k' u' v' - oz z (Function.update a k u) k' u' v' =
      oz z (Function.update a k' v') k u v - oz z (Function.update a k' u') k u v := by
  have e := hz _ (sq_sub ha hk.ne h.ne h'.ne hu hv hu' hv')
  rw [constD_sq z a k k' hk u v u' v' h h'] at e
  rw [oz_of_lt z h', oz_of_lt z h', oz_of_lt z h, oz_of_lt z h, ← sub_eq_zero, ← e]
  abel

theorem oz_sq_lt {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k k' : K} (hk : k < k') {u v : ι k} {u' v' : ι k'}
    (hu : u ∈ G k) (hv : v ∈ G k) (hu' : u' ∈ G k') (hv' : v' ∈ G k') :
    oz z (Function.update a k v) k' u' v' - oz z (Function.update a k u) k' u' v' =
      oz z (Function.update a k' v') k u v - oz z (Function.update a k' u') k u v := by
  have step : ∀ p q : ι k, p ∈ G k → q ∈ G k → p < q →
      oz z (Function.update a k q) k' u' v' - oz z (Function.update a k p) k' u' v' =
        oz z (Function.update a k' v') k p q - oz z (Function.update a k' u') k p q := by
    intro p q hp hq hpq
    rcases lt_trichotomy u' v' with h' | rfl | h'
    · exact oz_sq_core z hz ha hk hpq h' hp hq hu' hv'
    · simp [oz_self]
    · have c := oz_sq_core z hz ha hk hpq h' hp hq hv' hu'
      rw [oz_swap z (Function.update a k q) k' v' u', oz_swap z (Function.update a k p) k' v' u']
      rw [← sub_eq_zero] at c ⊢
      rw [← neg_eq_zero, ← c]
      abel
  rcases lt_trichotomy u v with h | rfl | h
  · exact step u v hu hv h
  · simp [oz_self]
  · have c := step v u hv hu h
    rw [oz_swap z (Function.update a k' v') k v u, oz_swap z (Function.update a k' u') k v u]
    rw [← sub_eq_zero] at c ⊢
    rw [← neg_eq_zero, ← c]
    abel

theorem oz_sq {a : ∀ k, ι k} (ha : ∀ l, a l ∈ G l) {k k' : K} (hk : k ≠ k') {u v : ι k} {u' v' : ι k'}
    (hu : u ∈ G k) (hv : v ∈ G k) (hu' : u' ∈ G k') (hv' : v' ∈ G k') :
    oz z (Function.update a k v) k' u' v' - oz z (Function.update a k u) k' u' v' =
      oz z (Function.update a k' v') k u v - oz z (Function.update a k' u') k u v := by
  rcases lt_or_gt_of_ne hk with h | h
  · exact oz_sq_lt z hz ha h hu hv hu' hv'
  · exact (oz_sq_lt z hz ha h hu' hv' hu hv).symm

end Square

def mix (e b : ∀ k, ι k) (s : Finset K) : ∀ k, ι k := fun l => if l ∈ s then b l else e l

theorem mix_mem {G : ∀ k, Finset (ι k)} {e b : ∀ k, ι k} (he : ∀ l, e l ∈ G l) (hb : ∀ l, b l ∈ G l)
    (s : Finset K) : ∀ l, mix e b s l ∈ G l := by
  intro l
  unfold mix
  split_ifs
  · exact hb l
  · exact he l

theorem sum_initial (g : Finset K → V) (s : Finset K) :
    ∑ m ∈ s, (g (s.filter (· ≤ m)) - g (s.filter (· < m))) = g s - g ∅ := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert has]
    have e1 : (insert a s).filter (· ≤ a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact (ha x hx).le
    have e2 : (insert a s).filter (· < a) = s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · intro hx
        exact ⟨Or.inr hx, ha x hx⟩
    have e3 : ∀ m ∈ s, (insert a s).filter (· ≤ m) = s.filter (· ≤ m) := fun m hm => by
      rw [Finset.filter_insert, if_neg (not_le.mpr (ha m hm))]
    have e4 : ∀ m ∈ s, (insert a s).filter (· < m) = s.filter (· < m) := fun m hm => by
      rw [Finset.filter_insert, if_neg (not_lt.mpr (ha m hm).le)]
    rw [e1, e2, Finset.sum_congr rfl (fun m hm => by rw [e3 m hm, e4 m hm]), ih]
    abel

def pathF (z : Cell K ι 1 → V) (e b : ∀ k, ι k) : V :=
  ∑ m, oz z (mix e b (Finset.univ.filter (· < m))) m (e m) (b m)

def gpath (z : Cell K ι 1 → V) (e a : ∀ k, ι k) (k : K) (u v : ι k) (s : Finset K) : V :=
  if k ∈ s then oz z (mix e a s) k u v else 0

section Path

variable (z : Cell K ι 1 → V) {G : ∀ k, Finset (ι k)}
  (hz : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0)
  {e a : ∀ k, ι k} (he : ∀ l, e l ∈ G l) (ha : ∀ l, a l ∈ G l) {k : K} {u v : ι k} (hu : u ∈ G k) (hv : v ∈ G k)
include hz he ha hu hv

theorem term_lt {m : K} (hmk : m < k) :
    oz z (mix e (Function.update a k v) (Finset.univ.filter (· < m))) m (e m) (Function.update a k v m) -
      oz z (mix e (Function.update a k u) (Finset.univ.filter (· < m))) m (e m) (Function.update a k u m) =
      gpath z e a k u v (Finset.univ.filter (· ≤ m)) - gpath z e a k u v (Finset.univ.filter (· < m)) := by
  have h3 : mix e (Function.update a k v) (Finset.univ.filter (· < m)) =
      mix e (Function.update a k u) (Finset.univ.filter (· < m)) := by
    funext l
    by_cases hl : l < m
    · simp [mix, hl, Function.update_of_ne (ne_of_lt (hl.trans hmk))]
    · simp [mix, hl]
  rw [h3, Function.update_of_ne (ne_of_lt hmk), Function.update_of_ne (ne_of_lt hmk), sub_self]
  simp [gpath, not_le.mpr hmk, not_lt.mpr hmk.le]

theorem term_eq :
    oz z (mix e (Function.update a k v) (Finset.univ.filter (· < k))) k (e k) (Function.update a k v k) -
      oz z (mix e (Function.update a k u) (Finset.univ.filter (· < k))) k (e k) (Function.update a k u k) =
      gpath z e a k u v (Finset.univ.filter (· ≤ k)) - gpath z e a k u v (Finset.univ.filter (· < k)) := by
  have hB : ∀ x : ι k, ∀ l, l ≠ k → mix e (Function.update a k x) (Finset.univ.filter (· < k)) l =
      mix e a (Finset.univ.filter (· < k)) l := by
    intro x l hl
    simp [mix, Function.update_of_ne hl]
  have hC : ∀ l, l ≠ k → mix e a (Finset.univ.filter (· ≤ k)) l = mix e a (Finset.univ.filter (· < k)) l := by
    intro l hl
    simp [mix, le_iff_lt_or_eq, hl]
  rw [Function.update_self, Function.update_self, oz_congr z _ _ (hB v), oz_congr z _ _ (hB u),
    oz_tri z hz (mix_mem he ha _) (he k) hu hv]
  simp only [gpath, Finset.mem_filter, Finset.mem_univ, true_and, le_refl, if_true, lt_irrefl, if_false,
    sub_zero]
  exact (oz_congr z u v hC).symm

theorem term_gt {m : K} (hkm : k < m) :
    oz z (mix e (Function.update a k v) (Finset.univ.filter (· < m))) m (e m) (Function.update a k v m) -
      oz z (mix e (Function.update a k u) (Finset.univ.filter (· < m))) m (e m) (Function.update a k u m) =
      gpath z e a k u v (Finset.univ.filter (· ≤ m)) - gpath z e a k u v (Finset.univ.filter (· < m)) := by
  have hU : ∀ x : ι k, mix e (Function.update a k x) (Finset.univ.filter (· < m)) =
      Function.update (mix e a (Finset.univ.filter (· < m))) k x := by
    intro x
    funext l
    rcases eq_or_ne l k with rfl | hl
    · simp [mix, hkm]
    · simp [mix, Function.update_of_ne hl]
  have hA : Function.update (mix e a (Finset.univ.filter (· < m))) m (a m) =
      mix e a (Finset.univ.filter (· ≤ m)) := by
    funext l
    rcases eq_or_ne l m with rfl | hl
    · simp [mix]
    · simp [mix, le_iff_lt_or_eq, hl]
  have hE : Function.update (mix e a (Finset.univ.filter (· < m))) m (e m) =
      mix e a (Finset.univ.filter (· < m)) := by
    funext l
    rcases eq_or_ne l m with rfl | hl
    · simp [mix]
    · simp [Function.update_of_ne hl]
  rw [hU, hU, Function.update_of_ne (ne_of_gt hkm), Function.update_of_ne (ne_of_gt hkm),
    oz_sq z hz (mix_mem he ha _) (ne_of_lt hkm) hu hv (he m) (ha m), hA, hE]
  simp [gpath, hkm.le, hkm]

theorem pathF_edge :
    pathF z e (Function.update a k v) - pathF z e (Function.update a k u) = oz z a k u v := by
  unfold pathF
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ m, oz z (mix e (Function.update a k v) (Finset.univ.filter (· < m))) m (e m)
        (Function.update a k v m) -
      oz z (mix e (Function.update a k u) (Finset.univ.filter (· < m))) m (e m) (Function.update a k u m) =
      gpath z e a k u v (Finset.univ.filter (· ≤ m)) - gpath z e a k u v (Finset.univ.filter (· < m)) := by
    intro m
    rcases lt_trichotomy m k with h | rfl | h
    · exact term_lt z hz he ha hu hv h
    · exact term_eq z hz he ha hu hv
    · exact term_gt z hz he ha hu hv h
  rw [Finset.sum_congr rfl (fun m _ => hterm m), sum_initial]
  have hm : mix e a Finset.univ = a := funext fun l => by simp [mix]
  simp [gpath, hm]

end Path

theorem exists_edge (J : Cell K ι 1) : ∃ (a : ∀ k, ι k) (k : K) (u v : ι k) (h : u < v),
    (∀ l, a l ∈ J.1 l) ∧ u ∈ J.1 k ∧ v ∈ J.1 k ∧ J = edge a k u v h.ne := by
  rcases J with ⟨I, hne, hs⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun l => (I l).card - 1) (by rw [hs]; exact one_ne_zero)
  have hk1 : (I k).card - 1 ≤ 1 := hs ▸ Finset.single_le_sum (f := fun l => (I l).card - 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hk2 : (I k).card = 2 := by omega
  have ha : ∀ l, (hne l).choose ∈ I l := fun l => (hne l).choose_spec
  have hl1 : ∀ l, l ≠ k → I l = {(hne l).choose} := by
    intro l hl
    have h2 := Finset.sum_le_sum_of_subset (f := fun l => (I l).card - 1) (Finset.subset_univ {k, l})
    rw [Finset.sum_pair (Ne.symm hl), hs] at h2
    have hc : (I l).card = 1 := by have := (hne l).card_pos; omega
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨ha l, fun y hy => Finset.card_le_one.mp hc.le y hy _ (ha l)⟩
  obtain ⟨p, q, hpq, hpq'⟩ := Finset.card_eq_two.mp hk2
  rcases lt_or_gt_of_ne hpq with h | h
  · refine ⟨fun l => (hne l).choose, k, p, q, h, ha, by simp [hpq'], by simp [hpq'],
      Subtype.ext (funext fun l => ?_)⟩
    show I l = Function.update (fun l => ({(hne l).choose} : Finset (ι l))) k {p, q} l
    by_cases hl : l = k
    · subst hl; rw [Function.update_self, hpq']
    · rw [Function.update_of_ne hl]; exact hl1 l hl
  · refine ⟨fun l => (hne l).choose, k, q, p, h, ha, by simp [hpq'], by simp [hpq'],
      Subtype.ext (funext fun l => ?_)⟩
    show I l = Function.update (fun l => ({(hne l).choose} : Finset (ι l))) k {q, p} l
    by_cases hl : l = k
    · subst hl; rw [Function.update_self, hpq', Finset.pair_comm]
    · rw [Function.update_of_ne hl]; exact hl1 l hl

noncomputable def vtx (c : Cell K ι 0) : ∀ k, ι k := fun l => (c.2.1 l).choose

theorem vtx_pt (a : ∀ k, ι k) : vtx (pt a) = a :=
  funext fun l => Finset.mem_singleton.mp ((pt a).2.1 l).choose_spec

theorem full : CechConstVanish.Statement := by
  intro K _ _ ι _ V _ G z hz
  by_cases hG : ∀ k, (G k).Nonempty
  swap
  · simp only [not_forall, Finset.not_nonempty_iff_eq_empty] at hG
    obtain ⟨k, hk⟩ := hG
    refine ⟨0, fun J hJ => ?_⟩
    exfalso
    obtain ⟨i, hi⟩ := J.2.1 k
    have := hJ k hi
    rw [hk] at this
    simp at this
  choose e he using hG
  refine ⟨fun c => pathF z e (vtx c), fun J hJ => ?_⟩
  obtain ⟨a, k, u, v, huv, haJ, hu, hv, rfl⟩ := exists_edge J
  have ha : ∀ l, a l ∈ G l := fun l => hJ l (haJ l)
  rw [constD_edge _ a k u v huv, vtx_pt, vtx_pt, pathF_edge z hz he ha (hJ k hu) (hJ k hv), oz_of_lt z huv]

end CechConstVanish

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
