import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Lemmata.GeneralBFactLeftFurther.Imports

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

namespace B2

section Sets

variable {r K : ℕ}

def Jp (J : Finset (Fin (r + K))) : Finset (Fin r) := univ.filter fun a => Fin.castAdd K a ∈ J

def Jt (J : Finset (Fin (r + K))) : Finset (Fin K) := univ.filter fun b => Fin.natAdd r b ∈ J

@[simp] lemma mem_Jp {J : Finset (Fin (r + K))} {a : Fin r} : a ∈ Jp J ↔ Fin.castAdd K a ∈ J := by simp [Jp]

@[simp] lemma mem_Jt {J : Finset (Fin (r + K))} {b : Fin K} : b ∈ Jt J ↔ Fin.natAdd r b ∈ J := by simp [Jt]

lemma ca_ne_na (a : Fin r) (b : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r b := by
  intro h; have := congrArg Fin.val h; simp at this; omega

lemma sum_split {M : Type*} [AddCommMonoid M] (J : Finset (Fin (r + K))) (F : Fin (r + K) → M) :
    ∑ m ∈ J, F m = ∑ a ∈ Jp J, F (Fin.castAdd K a) + ∑ b ∈ Jt J, F (Fin.natAdd r b) := by
  rw [Jp, Jt, Finset.sum_filter, Finset.sum_filter, ← Fin.sum_univ_add (fun m => if m ∈ J then F m else 0)]
  simp

lemma card_split (J : Finset (Fin (r + K))) : J.card = (Jp J).card + (Jt J).card := by
  rw [Finset.card_eq_sum_ones, sum_split, ← Finset.card_eq_sum_ones, ← Finset.card_eq_sum_ones]

lemma Jp_card_le (J : Finset (Fin (r + K))) : (Jp J).card ≤ r := by
  simpa using Finset.card_le_univ (Jp J)

lemma Jp_erase_ca (J : Finset (Fin (r + K))) (a : Fin r) : Jp (J.erase (Fin.castAdd K a)) = (Jp J).erase a := by
  ext x; simp [Fin.castAdd_inj]

lemma Jt_erase_ca (J : Finset (Fin (r + K))) (a : Fin r) : Jt (J.erase (Fin.castAdd K a)) = Jt J := by
  ext x; simp [(ca_ne_na a x).symm]

lemma Jp_erase_na (J : Finset (Fin (r + K))) (b : Fin K) : Jp (J.erase (Fin.natAdd r b)) = Jp J := by
  ext x; simp [ca_ne_na x b]

lemma Jt_erase_na (J : Finset (Fin (r + K))) (b : Fin K) : Jt (J.erase (Fin.natAdd r b)) = (Jt J).erase b := by
  ext x; simp [Fin.natAdd_inj]

lemma Jp_insert_ca (J : Finset (Fin (r + K))) (a : Fin r) : Jp (insert (Fin.castAdd K a) J) = insert a (Jp J) := by
  ext x; simp [Fin.castAdd_inj]

lemma Jt_insert_ca (J : Finset (Fin (r + K))) (a : Fin r) : Jt (insert (Fin.castAdd K a) J) = Jt J := by
  ext x; simp [(ca_ne_na a x).symm]

lemma Jp_insert_na (J : Finset (Fin (r + K))) (b : Fin K) : Jp (insert (Fin.natAdd r b) J) = Jp J := by
  ext x; simp [ca_ne_na x b]

lemma Jt_insert_na (J : Finset (Fin (r + K))) (b : Fin K) : Jt (insert (Fin.natAdd r b) J) = insert b (Jt J) := by
  ext x; simp [Fin.natAdd_inj]

lemma Jp_compl (J : Finset (Fin (r + K))) : Jp (univ \ J) = univ \ Jp J := by
  ext x; simp

lemma Jt_compl (J : Finset (Fin (r + K))) : Jt (univ \ J) = univ \ Jt J := by
  ext x; simp

lemma card_filter_na (J : Finset (Fin (r + K))) (b : Fin K) :
    (J.filter fun j => Fin.natAdd r b < j).card = ((Jt J).filter fun b' => b < b').card := by
  rw [Finset.card_filter, sum_split, Finset.card_filter]
  have h1 : ∀ a : Fin r, ¬ (Fin.natAdd r b < Fin.castAdd K a) := by
    intro a h; rw [Fin.lt_def] at h; simp at h; omega
  have h2 : ∀ b' : Fin K, (Fin.natAdd r b < Fin.natAdd r b') ↔ b < b' := by
    intro b'; rw [Fin.lt_def, Fin.lt_def]; simp
  simp [h1, h2]

lemma card_filter_ca (J : Finset (Fin (r + K))) (a : Fin r) :
    (J.filter fun j => Fin.castAdd K a < j).card = ((Jp J).filter fun a' => a < a').card + (Jt J).card := by
  rw [Finset.card_filter, sum_split, Finset.card_filter]
  have h1 : ∀ b : Fin K, (Fin.castAdd K a < Fin.natAdd r b) := by
    intro b; rw [Fin.lt_def]; simp; omega
  have h2 : ∀ a' : Fin r, (Fin.castAdd K a < Fin.castAdd K a') ↔ a < a' := by
    intro a'; rw [Fin.lt_def, Fin.lt_def]; simp
  simp [h1, h2]

end Sets

section Orders

variable {σ : Type*} {R : Type*} [CommRing R] (wv : σ → ℕ)

def Ord (b : ℕ) (f : MvPolynomial σ R) : Prop := ∀ m, Finsupp.weight wv m < b → coeff m f = 0

def IsW (y : MvPolynomial σ R) (a : ℕ) : Prop := y = 0 ∨ ∃ v, y = X v ∧ wv v = a

variable {wv}

lemma Ord.zero (b : ℕ) : Ord wv b (0 : MvPolynomial σ R) := fun m _ => by simp

lemma Ord.mono {b b' : ℕ} {f : MvPolynomial σ R} (h : Ord wv b f) (hb : b' ≤ b) : Ord wv b' f :=
  fun m hm => h m (lt_of_lt_of_le hm hb)

lemma Ord.neg {b : ℕ} {f : MvPolynomial σ R} (h : Ord wv b f) : Ord wv b (-f) :=
  fun m hm => by simp [h m hm]

lemma Ord.sum {ι : Type*} {b : ℕ} {s : Finset ι} {f : ι → MvPolynomial σ R} (h : ∀ i ∈ s, Ord wv b (f i)) :
    Ord wv b (∑ i ∈ s, f i) := fun m hm => by
  rw [coeff_sum]; exact Finset.sum_eq_zero fun i hi => h i hi m hm

lemma Ord.add {b : ℕ} {f g : MvPolynomial σ R} (h : Ord wv b f) (h' : Ord wv b g) : Ord wv b (f + g) :=
  fun m hm => by simp [h m hm, h' m hm]

lemma weight_single_add (v : σ) (m : σ →₀ ℕ) :
    Finsupp.weight wv (Finsupp.single v 1 + m) = wv v + Finsupp.weight wv m := by
  rw [map_add, Finsupp.weight_single]; simp

lemma Ord.X_mul {b : ℕ} {f : MvPolynomial σ R} (h : Ord wv b f) (v : σ) : Ord wv (wv v + b) (X v * f) := by
  classical
  intro m hm
  rw [coeff_X_mul']
  split_ifs with hv
  · obtain ⟨m', rfl⟩ : ∃ m', m = Finsupp.single v 1 + m' :=
      ⟨m - Finsupp.single v 1, (add_tsub_cancel_of_le (by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))).symm⟩
    rw [weight_single_add] at hm
    rw [add_tsub_cancel_left]
    exact h m' (by omega)
  · rfl

lemma Ord.term {a b b' e : ℕ} {y f : MvPolynomial σ R} (hy : IsW wv y a) (h : Ord wv b f) (hb : b' ≤ a + b) :
    Ord wv b' ((-1) ^ e * y * f) := by
  rcases hy with rfl | ⟨v, rfl, rfl⟩
  · simpa using Ord.zero b'
  · rcases neg_one_pow_eq_or (MvPolynomial σ R) e with h1 | h1 <;> rw [h1]
    · simpa using (h.X_mul v).mono hb
    · simpa using ((h.X_mul v).mono hb).neg

lemma cmp_of_Ord {b o : ℕ} {f : MvPolynomial σ R} (h : Ord wv b f) (ho : o < b) :
    weightedHomogeneousComponent wv o f = 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hm
  · simpa using h m (by omega)
  · simp

lemma cmp_X_mul (o : ℕ) (v : σ) (f : MvPolynomial σ R) :
    weightedHomogeneousComponent wv (wv v + o) (X v * f) = X v * weightedHomogeneousComponent wv o f := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_X_mul', coeff_X_mul']
  by_cases hv : v ∈ m.support
  · obtain ⟨m', rfl⟩ : ∃ m', m = Finsupp.single v 1 + m' :=
      ⟨m - Finsupp.single v 1, (add_tsub_cancel_of_le (by
        rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))).symm⟩
    rw [if_pos hv, if_pos hv, add_tsub_cancel_left, coeff_weightedHomogeneousComponent, weight_single_add]
    simp
  · simp [hv]

lemma cmp_term {a e : ℕ} (o : ℕ) {y : MvPolynomial σ R} (f : MvPolynomial σ R) (hy : IsW wv y a) :
    weightedHomogeneousComponent wv (a + o) ((-1) ^ e * y * f) =
      (-1) ^ e * y * weightedHomogeneousComponent wv o f := by
  rcases hy with rfl | ⟨v, rfl, rfl⟩
  · simp
  · rcases neg_one_pow_eq_or (MvPolynomial σ R) e with h1 | h1 <;> rw [h1]
    · simp [cmp_X_mul]
    · simp [cmp_X_mul]

end Orders

section Generic

def KG {n : ℕ} {P : Type*} [CommRing P] (c : ℤ) (hs : ℕ → ℕ) (x : ℕ → Fin n → P) : ℕ → Finset (Fin n) → P
  | 0 => extOne
  | j + 1 => colStep c (hs j) (hs (j + 1)) (x j) (KG c hs x j)

section KGbasic

variable {n : ℕ} {P : Type*} [CommRing P] {c : ℤ} {hs : ℕ → ℕ} {x : ℕ → Fin n → P} {j : ℕ}

lemma KG_rise_pos (hc : 1 ≤ c) (h : hs j < hs (j + 1)) : KG c hs x (j + 1) = wedgeR (x j) (KG c hs x j) := by
  show colStep c (hs j) (hs (j + 1)) (x j) (KG c hs x j) = _
  rw [colStep, if_pos h, if_pos hc]

lemma KG_fall_pos (hc : 1 ≤ c) (h : hs (j + 1) < hs j) : KG c hs x (j + 1) = contrR (x j) (KG c hs x j) := by
  show colStep c (hs j) (hs (j + 1)) (x j) (KG c hs x j) = _
  rw [colStep, if_neg (by omega), if_pos h, if_pos hc]

lemma KG_rise_neg (hc : ¬ 1 ≤ c) (h : hs j < hs (j + 1)) : KG c hs x (j + 1) = contrR (x j) (KG c hs x j) := by
  show colStep c (hs j) (hs (j + 1)) (x j) (KG c hs x j) = _
  rw [colStep, if_pos h, if_neg hc]

lemma KG_fall_neg (hc : ¬ 1 ≤ c) (h : hs (j + 1) < hs j) : KG c hs x (j + 1) = wedgeR (x j) (KG c hs x j) := by
  show colStep c (hs j) (hs (j + 1)) (x j) (KG c hs x j) = _
  rw [colStep, if_neg (by omega), if_pos h, if_neg hc]

lemma KG_eq (h : hs j = hs (j + 1)) : KG c hs x (j + 1) = KG c hs x j := by
  show colStep c (hs j) (hs (j + 1)) (x j) (KG c hs x j) = _
  rw [colStep, if_neg (by omega), if_neg (by omega)]

lemma wedgeR_ne {y : Fin n → P} {Kv : Finset (Fin n) → P} {J : Finset (Fin n)} (h : wedgeR y Kv J ≠ 0) :
    ∃ m ∈ J, Kv (J.erase m) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (Finset.sum_eq_zero fun m hm => by rw [hcon m hm, mul_zero])

lemma contrR_ne {y : Fin n → P} {Kv : Finset (Fin n) → P} {J : Finset (Fin n)} (h : contrR y Kv J ≠ 0) :
    ∃ m, m ∉ J ∧ Kv (insert m J) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (Finset.sum_eq_zero fun m hm => by rw [hcon m (by simpa using hm), mul_zero])

lemma extOne_ne {J : Finset (Fin n)} (h : (extOne J : P) ≠ 0) : J = ∅ := by
  by_contra hJ; exact h (by simp [extOne, hJ])

lemma KG_card_pos (hc : 1 ≤ c) (x : ℕ → Fin n → P) (h0 : hs 0 = 0)
    (hst : ∀ j, hs (j + 1) ≤ hs j + 1 ∧ hs j ≤ hs (j + 1) + 1) :
    ∀ (j : ℕ) (J : Finset (Fin n)), KG c hs x j J ≠ 0 → J.card = hs j
  | 0, J, h => by rw [extOne_ne h, h0]; rfl
  | j + 1, J, h => by
    have ih := KG_card_pos hc x h0 hst j
    have hj := hst j
    rcases lt_trichotomy (hs j) (hs (j + 1)) with h1 | h1 | h1
    · rw [KG_rise_pos hc h1] at h
      obtain ⟨m, hm, hK⟩ := wedgeR_ne h
      have h2 := ih _ hK
      rw [Finset.card_erase_of_mem hm] at h2
      have h3 := Finset.card_pos.mpr ⟨m, hm⟩
      omega
    · rw [KG_eq h1] at h
      rw [ih _ h, h1]
    · rw [KG_fall_pos hc h1] at h
      obtain ⟨m, hm, hK⟩ := contrR_ne h
      have h2 := ih _ hK
      rw [Finset.card_insert_of_notMem hm] at h2
      omega

end KGbasic

variable {σ : Type*} {R : Type*} [CommRing R] {wv : σ → ℕ} {r K : ℕ}

lemma ordWedge {Kj : Finset (Fin (r + K)) → MvPolynomial σ R} {y : Fin (r + K) → MvPolynomial σ R}
    {J : Finset (Fin (r + K))} {b : ℕ}
    (hp : ∀ a ∈ Jp J, ∀ e, Ord wv b ((-1) ^ e * y (Fin.castAdd K a) * Kj (J.erase (Fin.castAdd K a))))
    (ht : ∀ a ∈ Jt J, ∀ e, Ord wv b ((-1) ^ e * y (Fin.natAdd r a) * Kj (J.erase (Fin.natAdd r a)))) :
    Ord wv b (wedgeR y Kj J) := by
  unfold wedgeR
  rw [sum_split]
  exact (Ord.sum fun a ha => hp a ha _).add (Ord.sum fun a ha => ht a ha _)

lemma ordContr {Kj : Finset (Fin (r + K)) → MvPolynomial σ R} {y : Fin (r + K) → MvPolynomial σ R}
    {J : Finset (Fin (r + K))} {b : ℕ}
    (hp : ∀ a, a ∉ Jp J → ∀ e, Ord wv b ((-1) ^ e * y (Fin.castAdd K a) * Kj (insert (Fin.castAdd K a) J)))
    (ht : ∀ a, a ∉ Jt J → ∀ e, Ord wv b ((-1) ^ e * y (Fin.natAdd r a) * Kj (insert (Fin.natAdd r a) J))) :
    Ord wv b (contrR y Kj J) := by
  unfold contrR
  rw [sum_split, Jp_compl, Jt_compl]
  exact (Ord.sum fun a ha => hp a (by simpa using ha) _).add (Ord.sum fun a ha => ht a (by simpa using ha) _)

lemma wedge_tan {o cost : ℕ} {Kj : Finset (Fin (r + K)) → MvPolynomial σ R} {pl : Finset (Fin r) → MvPolynomial σ R}
    {tn : Finset (Fin K) → MvPolynomial σ R} {y : Fin (r + K) → MvPolynomial σ R}
    (hD : ∀ J, weightedHomogeneousComponent wv o (Kj J) = pl (Jp J) * tn (Jt J))
    (hyt : ∀ b, IsW wv (y (Fin.natAdd r b)) cost)
    (hoff : ∀ J, ∀ a ∈ Jp J, ∀ e,
      Ord wv (cost + o + 1) ((-1) ^ e * y (Fin.castAdd K a) * Kj (J.erase (Fin.castAdd K a))))
    (J : Finset (Fin (r + K))) :
    weightedHomogeneousComponent wv (cost + o) (wedgeR y Kj J) =
      pl (Jp J) * wedgeR (fun b => y (Fin.natAdd r b)) tn (Jt J) := by
  unfold wedgeR
  rw [sum_split, map_add, map_sum, map_sum,
    Finset.sum_eq_zero (fun a ha => cmp_of_Ord (hoff J a ha _) (Nat.lt_succ_self _)), zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [cmp_term o _ (hyt b), hD, Jp_erase_na, Jt_erase_na, card_filter_na]
  ring

lemma contr_tan {o cost : ℕ} {Kj : Finset (Fin (r + K)) → MvPolynomial σ R} {pl : Finset (Fin r) → MvPolynomial σ R}
    {tn : Finset (Fin K) → MvPolynomial σ R} {y : Fin (r + K) → MvPolynomial σ R}
    (hD : ∀ J, weightedHomogeneousComponent wv o (Kj J) = pl (Jp J) * tn (Jt J))
    (hyt : ∀ b, IsW wv (y (Fin.natAdd r b)) cost)
    (hoff : ∀ J, ∀ a, a ∉ Jp J → ∀ e,
      Ord wv (cost + o + 1) ((-1) ^ e * y (Fin.castAdd K a) * Kj (insert (Fin.castAdd K a) J)))
    (J : Finset (Fin (r + K))) :
    weightedHomogeneousComponent wv (cost + o) (contrR y Kj J) =
      pl (Jp J) * contrR (fun b => y (Fin.natAdd r b)) tn (Jt J) := by
  unfold contrR
  rw [sum_split, Jp_compl, Jt_compl, map_add, map_sum, map_sum,
    Finset.sum_eq_zero (fun a ha => cmp_of_Ord (hoff J a (by simpa using ha) _) (Nat.lt_succ_self _)), zero_add,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [cmp_term o _ (hyt b), hD, Jp_insert_na, Jt_insert_na, card_filter_na]
  ring

lemma wedge_pl {o cost : ℕ} {Kj : Finset (Fin (r + K)) → MvPolynomial σ R} {pl : Finset (Fin r) → MvPolynomial σ R}
    {tn : Finset (Fin K) → MvPolynomial σ R} {y : Fin (r + K) → MvPolynomial σ R}
    (hD : ∀ J, weightedHomogeneousComponent wv o (Kj J) = pl (Jp J) * tn (Jt J))
    (hyp : ∀ a, IsW wv (y (Fin.castAdd K a)) cost)
    (hoff : ∀ J, ∀ b ∈ Jt J, ∀ e,
      Ord wv (cost + o + 1) ((-1) ^ e * y (Fin.natAdd r b) * Kj (J.erase (Fin.natAdd r b))))
    (htn : ∀ J'', J'' ≠ ∅ → tn J'' = 0)
    (J : Finset (Fin (r + K))) :
    weightedHomogeneousComponent wv (cost + o) (wedgeR y Kj J) =
      wedgeR (fun a => y (Fin.castAdd K a)) pl (Jp J) * tn (Jt J) := by
  unfold wedgeR
  rw [sum_split, map_add, map_sum, map_sum,
    Finset.sum_eq_zero (s := Jt J) (fun a ha => cmp_of_Ord (hoff J a ha _) (Nat.lt_succ_self _)), add_zero,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [cmp_term o _ (hyp a), hD, Jp_erase_ca, Jt_erase_ca, card_filter_ca]
  by_cases hJ : Jt J = ∅
  · rw [hJ]; simp; ring
  · rw [htn _ hJ]; simp

lemma contr_pl {o cost : ℕ} {Kj : Finset (Fin (r + K)) → MvPolynomial σ R} {pl : Finset (Fin r) → MvPolynomial σ R}
    {tn : Finset (Fin K) → MvPolynomial σ R} {y : Fin (r + K) → MvPolynomial σ R}
    (hD : ∀ J, weightedHomogeneousComponent wv o (Kj J) = pl (Jp J) * tn (Jt J))
    (hyp : ∀ a, IsW wv (y (Fin.castAdd K a)) cost)
    (hoff : ∀ J, ∀ b, b ∉ Jt J → ∀ e,
      Ord wv (cost + o + 1) ((-1) ^ e * y (Fin.natAdd r b) * Kj (insert (Fin.natAdd r b) J)))
    (htn : ∀ J'', J'' ≠ ∅ → tn J'' = 0)
    (J : Finset (Fin (r + K))) :
    weightedHomogeneousComponent wv (cost + o) (contrR y Kj J) =
      contrR (fun a => y (Fin.castAdd K a)) pl (Jp J) * tn (Jt J) := by
  unfold contrR
  rw [sum_split, Jp_compl, Jt_compl, map_add, map_sum, map_sum,
    Finset.sum_eq_zero (s := univ \ Jt J)
      (fun a ha => cmp_of_Ord (hoff J a (by simpa using ha) _) (Nat.lt_succ_self _)), add_zero,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [cmp_term o _ (hyp a), hD, Jp_insert_ca, Jt_insert_ca, card_filter_ca]
  by_cases hJ : Jt J = ∅
  · rw [hJ]; simp; ring
  · rw [htn _ hJ]; simp

lemma cmp_one : weightedHomogeneousComponent wv 0 (1 : MvPolynomial σ R) = 1 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_one]
  split_ifs with h1 h2 h2
  · rfl
  · rfl
  · subst h2; simp at h1
  · rfl

lemma eq_empty_iff_split (J : Finset (Fin (r + K))) : J = ∅ ↔ Jp J = ∅ ∧ Jt J = ∅ := by
  rw [← Finset.card_eq_zero, ← Finset.card_eq_zero, ← Finset.card_eq_zero, card_split]; omega

lemma cmp_extOne (J : Finset (Fin (r + K))) :
    weightedHomogeneousComponent wv 0 (extOne J : MvPolynomial σ R) = extOne (Jp J) * extOne (Jt J) := by
  unfold extOne
  by_cases h : J = ∅
  · have h' := (eq_empty_iff_split J).mp h
    rw [if_pos h, if_pos h'.1, if_pos h'.2, cmp_one, mul_one]
  · rw [if_neg h, map_zero]
    by_cases h1 : Jp J = ∅
    · have h2 : Jt J ≠ ∅ := fun h2 => h ((eq_empty_iff_split J).mpr ⟨h1, h2⟩)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma ar0 {d d' w om : ℕ} (h : d' ≤ d) (hw : w ≤ om) : d' * w ≤ d * (om + 1) := Nat.mul_le_mul h (by omega)

lemma ar1 {d d' w om : ℕ} (h : d' ≤ d + 1) (hw : w ≤ om) : d' * w ≤ om + d * (om + 1) := by
  calc d' * w ≤ (d + 1) * om := Nat.mul_le_mul h hw
    _ = om + d * om := by ring
    _ ≤ om + d * (om + 1) := by nlinarith

lemma ar2 {d d' w om : ℕ} (h : d' + 1 ≤ d) (hw : w ≤ om) : om + d' * w ≤ d * (om + 1) := by
  calc om + d' * w ≤ om + d' * (om + 1) := by have := ar0 (le_refl d') hw; omega
    _ ≤ (d' + 1) * (om + 1) := by nlinarith
    _ ≤ d * (om + 1) := Nat.mul_le_mul h le_rfl

lemma ar3 {d om : ℕ} (h : 1 ≤ d) : om + 1 ≤ d * (om + 1) := Nat.le_mul_of_pos_left _ h

structure Dat (N r K : ℕ) (σ : Type*) (R : Type*) [CommRing R] (wv : σ → ℕ) where
  hs : ℕ → ℕ
  vec : ℕ → Bool
  om : ℕ → ℕ
  x : ℕ → Fin (r + K) → MvPolynomial σ R
  hxp : ∀ j a, IsW wv (x j (Fin.castAdd K a)) (if vec j then 0 else om j)
  hxt : ∀ j b, IsW wv (x j (Fin.natAdd r b)) (if vec j then om j else 0)
  hstep : ∀ j, if vec j then hs j ≤ hs (j + 1) ∧ hs (j + 1) ≤ hs j + 1 else hs (j + 1) ≤ hs j ∧ hs j ≤ hs (j + 1) + 1
  hom : ∀ i j, i < j → j < N → om j < om i
  hpos : ∀ j, j < N → 0 < om j

namespace Dat

variable {N : ℕ} (d : Dat N r K σ R wv) (c : ℤ)

def cost (j : ℕ) : ℕ :=
  if (d.hs j < d.hs (j + 1) ∧ r ≤ d.hs j) ∨ (d.hs (j + 1) < d.hs j ∧ d.hs j ≤ r) then d.om j else 0

def o (j : ℕ) : ℕ := ∑ i ∈ range j, d.cost i

def Kf (j : ℕ) : Finset (Fin (r + K)) → MvPolynomial σ R := KG c d.hs d.x j

def pl (j : ℕ) : Finset (Fin r) → MvPolynomial σ R :=
  KG c (fun j => min (d.hs j) r) (fun j a => d.x j (Fin.castAdd K a)) j

def tn (j : ℕ) : Finset (Fin K) → MvPolynomial σ R :=
  KG c (fun j => d.hs j - r) (fun j b => d.x j (Fin.natAdd r b)) j

lemma hst2 (j : ℕ) : d.hs (j + 1) ≤ d.hs j + 1 ∧ d.hs j ≤ d.hs (j + 1) + 1 := by
  have := d.hstep j
  split_ifs at this <;> omega

lemma vec_of_rise {j : ℕ} (h : d.hs j < d.hs (j + 1)) : d.vec j = true := by
  have hst := d.hstep j
  by_contra hv
  rw [if_neg hv] at hst
  omega

lemma vec_of_fall {j : ℕ} (h : d.hs (j + 1) < d.hs j) : ¬ (d.vec j = true) := by
  have hst := d.hstep j
  intro hv
  rw [if_pos hv] at hst
  omega

lemma o_succ (j : ℕ) : d.o (j + 1) = d.cost j + d.o j := by
  rw [o, Finset.sum_range_succ, add_comm]; rfl

theorem inv_pos (hc : 1 ≤ c) (h0 : d.hs 0 = 0) : ∀ j, j ≤ N →
    (∀ w, (∀ i, i < j → w ≤ d.om i) → ∀ J,
      Ord wv (d.o j + (min (d.hs j) r - (Jp J).card) * w) (d.Kf c j J)) ∧
    ∀ J, weightedHomogeneousComponent wv (d.o j) (d.Kf c j J) = d.pl c j (Jp J) * d.tn c j (Jt J) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun w _ J m hm => ?_, fun J => ?_⟩
    · exfalso; simp [o, h0] at hm
    · have h00 : d.o 0 = 0 := by simp [o]
      rw [h00]
      exact cmp_extOne (wv := wv) (R := R) J
  | succ j ih =>
    intro hj
    obtain ⟨ihA, ihD⟩ := ih (by omega)
    have hjN : j < N := by omega
    have hpos := d.hpos j hjN
    have A' := ihA (d.om j + 1) (fun i hi => d.hom i j hi hjN)
    have A0 : ∀ J, Ord wv (d.o j) (d.Kf c j J) := fun J => (A' J).mono (Nat.le_add_right _ _)
    have hcardK : ∀ J, d.Kf c j J ≠ 0 → J.card = d.hs j := KG_card_pos hc d.x h0 d.hst2 j
    have hcardT : ∀ J'', d.tn c j J'' ≠ 0 → J''.card = d.hs j - r :=
      KG_card_pos hc _ (by simp [h0]) (fun j => by have := d.hst2 j; omega) j
    have hs2 := d.hst2 j
    have ho := d.o_succ j
    rcases lt_trichotomy (d.hs j) (d.hs (j + 1)) with h1 | h1 | h1
    · have hv := d.vec_of_rise h1
      have hxp : ∀ a, IsW wv (d.x j (Fin.castAdd K a)) 0 := fun a => by
        have := d.hxp j a; rwa [if_pos hv] at this
      have hxt : ∀ b, IsW wv (d.x j (Fin.natAdd r b)) (d.om j) := fun b => by
        have := d.hxt j b; rwa [if_pos hv] at this
      have hK : d.Kf c (j + 1) = wedgeR (d.x j) (d.Kf c j) := KG_rise_pos hc h1
      by_cases h2 : d.hs j < r
      · have hcost : d.cost j = 0 := by rw [cost, if_neg (by omega)]
        have hpl : d.pl c (j + 1) = wedgeR (fun a => d.x j (Fin.castAdd K a)) (d.pl c j) :=
          KG_rise_pos hc (by show min _ _ < min _ _; omega)
        have htn : d.tn c (j + 1) = d.tn c j := KG_eq (by show _ - _ = _ - _; omega)
        have htz : ∀ J'', J'' ≠ ∅ → d.tn c j J'' = 0 := fun J'' hJ => by
          by_contra hne
          have := hcardT J'' hne
          exact hJ (Finset.card_eq_zero.mp (by omega))
        refine ⟨fun w hw J => ?_, fun J => ?_⟩
        · have hwom := hw j (Nat.lt_succ_self j)
          rw [hK, ho, hcost]
          refine ordWedge (fun a ha e => ?_) (fun b hb e => ?_)
          · refine Ord.term (hxp a) (A' _) ?_
            rw [Jp_erase_ca, Finset.card_erase_of_mem ha]
            have h3 := Finset.card_pos.mpr ⟨a, ha⟩
            have := ar0 (d' := min (d.hs (j + 1)) r - (Jp J).card) (d := min (d.hs j) r - ((Jp J).card - 1))
              (by omega) hwom
            omega
          · refine Ord.term (hxt b) (A' _) ?_
            rw [Jp_erase_na]
            have := ar1 (d' := min (d.hs (j + 1)) r - (Jp J).card) (d := min (d.hs j) r - (Jp J).card)
              (by omega) hwom
            omega
        · rw [hK, hpl, htn, ho, hcost]
          exact wedge_pl ihD hxp (fun J b hb e => Ord.term (hxt b) (A0 _) (by omega)) htz J
      · have hcost : d.cost j = d.om j := by rw [cost, if_pos (by omega)]
        have hpl : d.pl c (j + 1) = d.pl c j := KG_eq (by show min _ _ = min _ _; omega)
        have htn : d.tn c (j + 1) = wedgeR (fun b => d.x j (Fin.natAdd r b)) (d.tn c j) :=
          KG_rise_pos hc (by show _ - _ < _ - _; omega)
        refine ⟨fun w hw J => ?_, fun J => ?_⟩
        · have hwom := hw j (Nat.lt_succ_self j)
          rw [hK, ho, hcost]
          refine ordWedge (fun a ha e => ?_) (fun b hb e => ?_)
          · refine Ord.term (hxp a) (A' _) ?_
            rw [Jp_erase_ca, Finset.card_erase_of_mem ha]
            have h3 := Finset.card_pos.mpr ⟨a, ha⟩
            have h4 := Jp_card_le J
            have := ar2 (d' := min (d.hs (j + 1)) r - (Jp J).card) (d := min (d.hs j) r - ((Jp J).card - 1))
              (by omega) hwom
            omega
          · refine Ord.term (hxt b) (A' _) ?_
            rw [Jp_erase_na]
            have := ar0 (d' := min (d.hs (j + 1)) r - (Jp J).card) (d := min (d.hs j) r - (Jp J).card)
              (by omega) hwom
            omega
        · rw [hK, hpl, htn, ho, hcost]
          refine wedge_tan ihD hxt (fun J a ha e => Ord.term (hxp a) (A' _) ?_) J
          rw [Jp_erase_ca, Finset.card_erase_of_mem ha]
          have h3 := Finset.card_pos.mpr ⟨a, ha⟩
          have h4 := Jp_card_le J
          have := ar3 (d := min (d.hs j) r - ((Jp J).card - 1)) (om := d.om j) (by omega)
          omega
    · have hcost : d.cost j = 0 := by rw [cost, if_neg (by omega)]
      have hK : d.Kf c (j + 1) = d.Kf c j := KG_eq h1
      have hpl : d.pl c (j + 1) = d.pl c j := KG_eq (by show min _ _ = min _ _; omega)
      have htn : d.tn c (j + 1) = d.tn c j := KG_eq (by show _ - _ = _ - _; omega)
      refine ⟨fun w hw J => ?_, fun J => ?_⟩
      · rw [hK, ho, hcost, ← h1, zero_add]
        exact ihA w (fun i hi => hw i (by omega)) J
      · rw [hK, hpl, htn, ho, hcost, zero_add]
        exact ihD J
    · have hv := d.vec_of_fall h1
      have hxp : ∀ a, IsW wv (d.x j (Fin.castAdd K a)) (d.om j) := fun a => by
        have := d.hxp j a; rwa [if_neg hv] at this
      have hxt : ∀ b, IsW wv (d.x j (Fin.natAdd r b)) 0 := fun b => by
        have := d.hxt j b; rwa [if_neg hv] at this
      have hK : d.Kf c (j + 1) = contrR (d.x j) (d.Kf c j) := KG_fall_pos hc h1
      by_cases h2 : r < d.hs j
      · have hcost : d.cost j = 0 := by rw [cost, if_neg (by omega)]
        have hpl : d.pl c (j + 1) = d.pl c j := KG_eq (by show min _ _ = min _ _; omega)
        have htn : d.tn c (j + 1) = contrR (fun b => d.x j (Fin.natAdd r b)) (d.tn c j) :=
          KG_fall_pos hc (by show _ - _ < _ - _; omega)
        refine ⟨fun w hw J => ?_, fun J => ?_⟩
        · have hwom := hw j (Nat.lt_succ_self j)
          rw [hK, ho, hcost]
          refine ordContr (fun a ha e => ?_) (fun b hb e => ?_)
          · refine Ord.term (hxp a) (A' _) ?_
            rw [Jp_insert_ca, Finset.card_insert_of_notMem ha]
            have := ar1 (d' := min (d.hs (j + 1)) r - (Jp J).card) (d := min (d.hs j) r - ((Jp J).card + 1))
              (by omega) hwom
            omega
          · refine Ord.term (hxt b) (A' _) ?_
            rw [Jp_insert_na]
            have := ar0 (d' := min (d.hs (j + 1)) r - (Jp J).card) (d := min (d.hs j) r - (Jp J).card)
              (by omega) hwom
            omega
        · rw [hK, hpl, htn, ho, hcost]
          exact contr_tan ihD hxt (fun J a ha e => Ord.term (hxp a) (A0 _) (by omega)) J
      · have hcost : d.cost j = d.om j := by rw [cost, if_pos (by omega)]
        have hpl : d.pl c (j + 1) = contrR (fun a => d.x j (Fin.castAdd K a)) (d.pl c j) :=
          KG_fall_pos hc (by show min _ _ < min _ _; omega)
        have htn : d.tn c (j + 1) = d.tn c j := KG_eq (by show _ - _ = _ - _; omega)
        have htz : ∀ J'', J'' ≠ ∅ → d.tn c j J'' = 0 := fun J'' hJ => by
          by_contra hne
          have := hcardT J'' hne
          exact hJ (Finset.card_eq_zero.mp (by omega))
        have hoffT : ∀ (J : Finset (Fin (r + K))) (b : Fin K), b ∉ Jt J → d.Kf c j (insert (Fin.natAdd r b) J) ≠ 0 →
            (Jp J).card + 1 ≤ d.hs j := fun J b hb hne => by
          have h5 := hcardK _ hne
          rw [Finset.card_insert_of_notMem (by simpa using hb), card_split] at h5
          omega
        refine ⟨fun w hw J => ?_, fun J => ?_⟩
        · have hwom := hw j (Nat.lt_succ_self j)
          rw [hK, ho, hcost]
          refine ordContr (fun a ha e => ?_) (fun b hb e => ?_)
          · refine Ord.term (hxp a) (A' _) ?_
            rw [Jp_insert_ca, Finset.card_insert_of_notMem ha]
            have := ar0 (d' := min (d.hs (j + 1)) r - (Jp J).card) (d := min (d.hs j) r - ((Jp J).card + 1))
              (by omega) hwom
            omega
          · by_cases hne : d.Kf c j (insert (Fin.natAdd r b) J) = 0
            · rw [hne, mul_zero]; exact Ord.zero _
            · have h5 := hoffT J b hb hne
              refine Ord.term (hxt b) (A' _) ?_
              rw [Jp_insert_na]
              have := ar2 (d' := min (d.hs (j + 1)) r - (Jp J).card) (d := min (d.hs j) r - (Jp J).card)
                (by omega) hwom
              omega
        · rw [hK, hpl, htn, ho, hcost]
          refine contr_pl ihD hxp (fun J b hb e => ?_) htz J
          by_cases hne : d.Kf c j (insert (Fin.natAdd r b) J) = 0
          · rw [hne, mul_zero]; exact Ord.zero _
          · have h5 := hoffT J b hb hne
            refine Ord.term (hxt b) (A' _) ?_
            rw [Jp_insert_na]
            have := ar3 (d := min (d.hs j) r - (Jp J).card) (om := d.om j) (by omega)
            omega

theorem inv_neg (hc : ¬ 1 ≤ c) (hr : ∀ j, j ≤ N → r ≤ d.hs j) : ∀ j, j ≤ N →
    (∀ w, (∀ i, i < j → w ≤ d.om i) → ∀ J, Ord wv (d.o j + (Jp J).card * w) (d.Kf c j J)) ∧
    ∀ J, weightedHomogeneousComponent wv (d.o j) (d.Kf c j J) = d.pl c j (Jp J) * d.tn c j (Jt J) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun w _ J => ?_, fun J => ?_⟩
    · by_cases hJ : J = ∅
      · subst hJ
        intro m hm
        exfalso; simp [o, Jp] at hm
      · show Ord wv _ (extOne J)
        rw [extOne, if_neg hJ]; exact Ord.zero _
    · have h00 : d.o 0 = 0 := by simp [o]
      rw [h00]
      exact cmp_extOne (wv := wv) (R := R) J
  | succ j ih =>
    intro hj
    obtain ⟨ihA, ihD⟩ := ih (by omega)
    have hjN : j < N := by omega
    have hpos := d.hpos j hjN
    have A' := ihA (d.om j + 1) (fun i hi => d.hom i j hi hjN)
    have A0 : ∀ J, Ord wv (d.o j) (d.Kf c j J) := fun J => (A' J).mono (Nat.le_add_right _ _)
    have hs2 := d.hst2 j
    have ho := d.o_succ j
    have hr1 := hr j (by omega)
    have hr2 := hr (j + 1) hj
    have hpl : d.pl c (j + 1) = d.pl c j := KG_eq (by show min _ _ = min _ _; omega)
    rcases lt_trichotomy (d.hs j) (d.hs (j + 1)) with h1 | h1 | h1
    · have hv := d.vec_of_rise h1
      have hxp : ∀ a, IsW wv (d.x j (Fin.castAdd K a)) 0 := fun a => by
        have := d.hxp j a; rwa [if_pos hv] at this
      have hxt : ∀ b, IsW wv (d.x j (Fin.natAdd r b)) (d.om j) := fun b => by
        have := d.hxt j b; rwa [if_pos hv] at this
      have hK : d.Kf c (j + 1) = contrR (d.x j) (d.Kf c j) := KG_rise_neg hc h1
      have hcost : d.cost j = d.om j := by rw [cost, if_pos (by omega)]
      have htn : d.tn c (j + 1) = contrR (fun b => d.x j (Fin.natAdd r b)) (d.tn c j) :=
        KG_rise_neg hc (by show _ - _ < _ - _; omega)
      refine ⟨fun w hw J => ?_, fun J => ?_⟩
      · have hwom := hw j (Nat.lt_succ_self j)
        rw [hK, ho, hcost]
        refine ordContr (fun a ha e => ?_) (fun b hb e => ?_)
        · refine Ord.term (hxp a) (A' _) ?_
          rw [Jp_insert_ca, Finset.card_insert_of_notMem ha]
          have := ar2 (d' := (Jp J).card) (d := (Jp J).card + 1) (by omega) hwom
          omega
        · refine Ord.term (hxt b) (A' _) ?_
          rw [Jp_insert_na]
          have := ar0 (d' := (Jp J).card) (d := (Jp J).card) (by omega) hwom
          omega
      · rw [hK, hpl, htn, ho, hcost]
        refine contr_tan ihD hxt (fun J a ha e => Ord.term (hxp a) (A' _) ?_) J
        rw [Jp_insert_ca, Finset.card_insert_of_notMem ha]
        have := ar3 (d := (Jp J).card + 1) (om := d.om j) (by omega)
        omega
    · have hcost : d.cost j = 0 := by rw [cost, if_neg (by omega)]
      have hK : d.Kf c (j + 1) = d.Kf c j := KG_eq h1
      have htn : d.tn c (j + 1) = d.tn c j := KG_eq (by show _ - _ = _ - _; omega)
      refine ⟨fun w hw J => ?_, fun J => ?_⟩
      · rw [hK, ho, hcost, zero_add]
        exact ihA w (fun i hi => hw i (by omega)) J
      · rw [hK, hpl, htn, ho, hcost, zero_add]
        exact ihD J
    · have hv := d.vec_of_fall h1
      have hxp : ∀ a, IsW wv (d.x j (Fin.castAdd K a)) (d.om j) := fun a => by
        have := d.hxp j a; rwa [if_neg hv] at this
      have hxt : ∀ b, IsW wv (d.x j (Fin.natAdd r b)) 0 := fun b => by
        have := d.hxt j b; rwa [if_neg hv] at this
      have hK : d.Kf c (j + 1) = wedgeR (d.x j) (d.Kf c j) := KG_fall_neg hc h1
      have hcost : d.cost j = 0 := by rw [cost, if_neg (by omega)]
      have htn : d.tn c (j + 1) = wedgeR (fun b => d.x j (Fin.natAdd r b)) (d.tn c j) :=
        KG_fall_neg hc (by show _ - _ < _ - _; omega)
      refine ⟨fun w hw J => ?_, fun J => ?_⟩
      · have hwom := hw j (Nat.lt_succ_self j)
        rw [hK, ho, hcost]
        refine ordWedge (fun a ha e => ?_) (fun b hb e => ?_)
        · refine Ord.term (hxp a) (A' _) ?_
          rw [Jp_erase_ca, Finset.card_erase_of_mem ha]
          have := ar1 (d' := (Jp J).card) (d := (Jp J).card - 1) (by omega) hwom
          omega
        · refine Ord.term (hxt b) (A' _) ?_
          rw [Jp_erase_na]
          have := ar0 (d' := (Jp J).card) (d := (Jp J).card) (by omega) hwom
          omega
      · rw [hK, hpl, htn, ho, hcost]
        exact wedge_tan ihD hxt (fun J a ha e => Ord.term (hxp a) (A0 _) (by omega)) J

lemma hs_ge (h0 : d.hs 0 = r + K) : ∀ j, r + K ≤ d.hs j + j
  | 0 => by omega
  | j + 1 => by have := hs_ge h0 j; have := d.hst2 j; omega

theorem low (hNK : N ≤ K) (h0 : if 1 ≤ c then d.hs 0 = 0 else d.hs 0 = r + K) (J : Finset (Fin (r + K))) :
    Ord wv (d.o N) (d.Kf c N J) ∧
    weightedHomogeneousComponent wv (d.o N) (d.Kf c N J) = d.pl c N (Jp J) * d.tn c N (Jt J) := by
  by_cases hc : 1 ≤ c
  · rw [if_pos hc] at h0
    obtain ⟨hA, hD⟩ := d.inv_pos c hc h0 N le_rfl
    exact ⟨by simpa using hA 0 (fun _ _ => Nat.zero_le _) J, hD J⟩
  · rw [if_neg hc] at h0
    obtain ⟨hA, hD⟩ := d.inv_neg c hc (fun j hj => by have := d.hs_ge h0 j; omega) N le_rfl
    exact ⟨by simpa using hA 0 (fun _ _ => Nat.zero_le _) J, hD J⟩

end Dat

end Generic

section Heights

lemma colH_spec {n : ℕ} {mu : Fin n → ℤ} (hd : Dominant mu) (c : ℤ) (m : Fin n) : c ≤ mu m ↔ m.val < colH mu c := by
  first | exact Bl.general_b_fact_left_further.goal1 .. | (apply Bl.general_b_fact_left_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_further.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_further.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_further.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_further.goal1 <;> first | assumption | infer_instance)

lemma colH_strip {n : ℕ} {nu mu : Fin n → ℤ} {b : ℕ} (hn : Dominant nu) (hm : Dominant mu) (h : HStrip nu mu b)
    (c : ℤ) : colH nu c ≤ colH mu c ∧ colH mu c ≤ colH nu c + 1 := by
  constructor
  · unfold colH
    refine Finset.card_le_card fun m hm' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
    exact hm'.trans (h.1 m)
  · by_contra hcon
    have hle := colH_le mu c
    have h1 : colH nu c + 1 < n := by omega
    have h2 : c ≤ mu ⟨colH nu c + 1, h1⟩ := (colH_spec hm c _).mpr (by show colH nu c + 1 < _; omega)
    have h3 := h.2.1 ⟨colH nu c, by omega⟩ h1
    have h4 := (colH_spec hn c ⟨colH nu c, by omega⟩).mp (h2.trans h3)
    simp at h4

variable {r K : ℕ}

lemma colH_pl {mu : Fin (r + K) → ℤ} (hd : Dominant mu) (c : ℤ) :
    colH (fun a : Fin r => mu (Fin.castAdd K a)) c = min (colH mu c) r := by
  have hd' : Dominant (fun a : Fin r => mu (Fin.castAdd K a)) := fun a a' h => hd (by
    rw [Fin.le_def] at h ⊢; simpa using h)
  have hle := colH_le (fun a : Fin r => mu (Fin.castAdd K a)) c
  have key : ∀ a : Fin r, a.val < colH (fun a : Fin r => mu (Fin.castAdd K a)) c ↔ a.val < colH mu c := fun a => by
    rw [← colH_spec hd' c a, colH_spec hd c (Fin.castAdd K a)]; simp
  rcases lt_trichotomy (colH (fun a : Fin r => mu (Fin.castAdd K a)) c) (min (colH mu c) r) with h | h | h
  · have := key ⟨colH (fun a : Fin r => mu (Fin.castAdd K a)) c, by omega⟩
    simp only at this; omega
  · exact h
  · have := key ⟨colH mu c, by omega⟩
    simp only at this; omega

lemma colH_tan {mu : Fin (r + K) → ℤ} (hd : Dominant mu) (c : ℤ) :
    colH (fun b : Fin K => mu (Fin.natAdd r b)) c = colH mu c - r := by
  have hd' : Dominant (fun b : Fin K => mu (Fin.natAdd r b)) := fun a a' h => hd (by
    rw [Fin.le_def] at h ⊢; simpa using h)
  have hle := colH_le (fun b : Fin K => mu (Fin.natAdd r b)) c
  have hle2 := colH_le mu c
  have key : ∀ b : Fin K, b.val < colH (fun b : Fin K => mu (Fin.natAdd r b)) c ↔ r + b.val < colH mu c := fun b => by
    rw [← colH_spec hd' c b, colH_spec hd c (Fin.natAdd r b)]; simp
  rcases lt_trichotomy (colH (fun b : Fin K => mu (Fin.natAdd r b)) c) (colH mu c - r) with h | h | h
  · have := key ⟨colH (fun b : Fin K => mu (Fin.natAdd r b)) c, by omega⟩
    simp only at this; omega
  · exact h
  · have := key ⟨colH mu c - r, by omega⟩
    simp only at this; omega

end Heights

section Translate

variable (R : Type*) [CommRing R] {N : ℕ}

def hsOf {n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (j : ℕ) : ℕ := colH (mu ⟨min j N, by omega⟩) c

def xOf (N n : ℕ) (j : ℕ) (m : Fin n) : MvPolynomial (Fin N × Fin n) R := if h : j < N then X (⟨j, h⟩, m) else 0

lemma hsOf_eq {n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (j : ℕ) (h : j < N + 1) :
    hsOf mu c j = colH (mu ⟨j, h⟩) c := by
  have : (⟨min j N, by omega⟩ : Fin (N + 1)) = ⟨j, h⟩ := Fin.ext (Nat.min_eq_left (by omega))
  rw [hsOf, this]

lemma Kcol_eq_KG {n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) :
    ∀ j, j ≤ N → Kcol R mu c j = KG c (hsOf mu c) (xOf R N n) j
  | 0, _ => rfl
  | j + 1, hj => by
    have hlt : j < N := hj
    rw [Kcol, dif_pos hlt, Kcol_eq_KG mu c j (by omega)]
    show _ = colStep c (hsOf mu c j) (hsOf mu c (j + 1)) (xOf R N n j) _
    rw [hsOf_eq mu c j (by omega), hsOf_eq mu c (j + 1) (by omega)]
    have : letVec R (⟨j, hlt⟩ : Fin N) = xOf R N n j := by
      funext m; simp [letVec, xOf, hlt]
    rw [this]

variable {R}

lemma map_KG {n : ℕ} {P Q : Type*} [CommRing P] [CommRing Q] (φ : P →+* Q) (c : ℤ) (hs : ℕ → ℕ)
    (x : ℕ → Fin n → P) : ∀ j J, φ (KG c hs x j J) = KG c hs (fun j m => φ (x j m)) j J
  | 0, J => by
    show φ (extOne J) = extOne J
    unfold extOne; split_ifs <;> simp
  | j + 1, J => by
    have ih := map_KG φ c hs x j
    show φ (colStep c (hs j) (hs (j + 1)) (x j) (KG c hs x j) J) =
      colStep c (hs j) (hs (j + 1)) (fun m => φ (x j m)) (KG c hs (fun j m => φ (x j m)) j) J
    unfold colStep
    split_ifs <;> simp [wedgeR, contrR, map_sum, ih]

end Translate

section Final

variable (R : Type*) [CommRing R] {N r K : ℕ}

def mkDat (LL : Letters (Fin N)) (B : Fin N → ℕ) (om : Fin N → ℕ) (hom : StrictAnti om) (hpos : ∀ i, 0 < om i)
    (P : PPath (r + K) N LL B) (c : ℤ) : Dat N r K (Fin N × Fin (r + K)) R (symWt (r := r) (K := K) LL om) where
  hs := hsOf P.mu c
  vec := fun j => if h : j < N then LL.vec ⟨j, h⟩ else true
  om := fun j => if h : j < N then om ⟨j, h⟩ else 0
  x := xOf R N (r + K)
  hxp := by
    intro j a
    by_cases h : j < N
    · refine Or.inr ⟨(⟨j, h⟩, Fin.castAdd K a), by simp [xOf, h], ?_⟩
      simp only [dif_pos h, symWt, Fin.val_castAdd]
      cases hv : LL.vec ⟨j, h⟩
      · simp
      · have := a.2
        simp
    · exact Or.inl (by simp [xOf, h])
  hxt := by
    intro j b
    by_cases h : j < N
    · refine Or.inr ⟨(⟨j, h⟩, Fin.natAdd r b), by simp [xOf, h], ?_⟩
      simp only [dif_pos h, symWt, Fin.val_natAdd]
      cases hv : LL.vec ⟨j, h⟩
      · simp
      · simp
    · exact Or.inl (by simp [xOf, h])
  hstep := by
    intro j
    by_cases h : j < N
    · rw [hsOf_eq P.mu c j (by omega), hsOf_eq P.mu c (j + 1) (by omega)]
      have hs := P.step ⟨j, h⟩
      simp only [dif_pos h]
      have e1 : (⟨j, h⟩ : Fin N).castSucc = ⟨j, by omega⟩ := rfl
      have e2 : (⟨j, h⟩ : Fin N).succ = ⟨j + 1, by omega⟩ := rfl
      rw [e1, e2] at hs
      split_ifs at hs ⊢ with hv
      · exact colH_strip (P.dom _) (P.dom _) hs c
      · exact colH_strip (P.dom _) (P.dom _) hs c
    · have : hsOf P.mu c j = hsOf P.mu c (j + 1) := by
        unfold hsOf
        have e : (⟨min j N, by omega⟩ : Fin (N + 1)) = ⟨min (j + 1) N, by omega⟩ := Fin.ext (by simp; omega)
        rw [e]
      rw [this]
      split_ifs <;> omega
  hom := by
    intro i j hij hj
    rw [dif_pos hj, dif_pos (by omega)]
    exact hom (by rw [Fin.lt_def]; exact hij)
  hpos := by
    intro j hj
    rw [dif_pos hj]; exact hpos _

lemma mkDat_o (LL : Letters (Fin N)) (B : Fin N → ℕ) (om : Fin N → ℕ) (hom : StrictAnti om) (hpos : ∀ i, 0 < om i)
    (P : PPath (r + K) N LL B) (c : ℤ) : (mkDat R LL B om hom hpos P c).o N = oc om P.mu c := by
  classical
  rw [Dat.o, Finset.sum_range, oc]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (mkDat R LL B om hom hpos P c).hs i = colH (P.mu i.castSucc) c := hsOf_eq P.mu c i (by omega)
  have e2 : (mkDat R LL B om hom hpos P c).hs (i + 1) = colH (P.mu i.succ) c := hsOf_eq P.mu c (i + 1) (by omega)
  have e3 : (mkDat R LL B om hom hpos P c).om i = om i := dif_pos i.2
  rw [Dat.cost, e1, e2, e3]
  by_cases hC : IsCostly P.mu c i
  · rw [if_pos hC]; exact if_pos hC
  · rw [if_neg hC]; exact if_neg hC

theorem kcol_low (LL : Letters (Fin N)) (B : Fin N → ℕ) (om : Fin N → ℕ) (hNK : N + r ≤ K) (hom : StrictAnti om)
    (hpos : ∀ i, 0 < om i) (P : PPath (r + K) N LL B) (c : ℤ) (J : Finset (Fin (r + K))) :
    (∀ m ∈ (Kcol R P.mu c N J).support, oc om P.mu c ≤ monWt LL om m) ∧
    weightedHomogeneousComponent (symWt (r := r) (K := K) LL om) (oc om P.mu c) (Kcol R P.mu c N J) =
      plTanCol R P.mu c J := by
  have h0 : if 1 ≤ c then (mkDat R LL B om hom hpos P c).hs 0 = 0
      else (mkDat R LL B om hom hpos P c).hs 0 = r + K := by
    have e0 : (mkDat R LL B om hom hpos P c).hs 0 = colH (P.mu 0) c := hsOf_eq P.mu c 0 (by omega)
    rw [e0, P.zero]
    unfold colH
    split_ifs with hc
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _; simp; omega
    · rw [Finset.filter_true_of_mem (fun m _ => by simp; omega)]; simp
  obtain ⟨hA, hD⟩ := (mkDat R LL B om hom hpos P c).low c (by omega) h0 J
  rw [mkDat_o] at hA hD
  have hK : (mkDat R LL B om hom hpos P c).Kf c N = Kcol R P.mu c N := (Kcol_eq_KG R P.mu c N le_rfl).symm
  rw [hK] at hA hD
  refine ⟨fun m hm => ?_, ?_⟩
  · by_contra hlt
    exact (MvPolynomial.mem_support_iff.mp hm) (hA m (not_le.mp hlt))
  · rw [hD]
    unfold plTanCol
    congr 1
    · rw [Kcol_eq_KG R (plPart P.mu) c N le_rfl]
      have := map_KG (rename (plVar (N := N) (r := r) (K := K)) :
        MvPolynomial (Fin N × Fin r) R →ₐ[R] MvPolynomial (Fin N × Fin (r + K)) R).toRingHom c
        (hsOf (plPart P.mu) c) (xOf R N r) N (Jp J)
      refine Eq.trans ?_ this.symm
      have e1 : hsOf (plPart P.mu) c = fun j => min ((mkDat R LL B om hom hpos P c).hs j) r := by
        funext j; exact colH_pl (P.dom _) c
      have e2 : (fun (j : ℕ) (m : Fin r) => (rename (plVar (N := N) (r := r) (K := K)) :
          MvPolynomial (Fin N × Fin r) R →ₐ[R] MvPolynomial (Fin N × Fin (r + K)) R).toRingHom (xOf R N r j m)) =
          fun j a => (mkDat R LL B om hom hpos P c).x j (Fin.castAdd K a) := by
        funext j a
        show (rename (plVar (N := N) (r := r) (K := K))) (xOf R N r j a) = xOf R N (r + K) j (Fin.castAdd K a)
        unfold xOf; split_ifs <;> simp [plVar]
      rw [e1, e2]; rfl
    · rw [Kcol_eq_KG R (tanPart P.mu) c N le_rfl]
      have := map_KG (rename (tanVar (N := N) (r := r) (K := K)) :
        MvPolynomial (Fin N × Fin K) R →ₐ[R] MvPolynomial (Fin N × Fin (r + K)) R).toRingHom c
        (hsOf (tanPart P.mu) c) (xOf R N K) N (Jt J)
      refine Eq.trans ?_ this.symm
      have e1 : hsOf (tanPart P.mu) c = fun j => (mkDat R LL B om hom hpos P c).hs j - r := by
        funext j; exact colH_tan (P.dom _) c
      have e2 : (fun (j : ℕ) (m : Fin K) => (rename (tanVar (N := N) (r := r) (K := K)) :
          MvPolynomial (Fin N × Fin K) R →ₐ[R] MvPolynomial (Fin N × Fin (r + K)) R).toRingHom (xOf R N K j m)) =
          fun j b => (mkDat R LL B om hom hpos P c).x j (Fin.natAdd r b) := by
        funext j b
        show (rename (tanVar (N := N) (r := r) (K := K))) (xOf R N K j b) = xOf R N (r + K) j (Fin.natAdd r b)
        unfold xOf; split_ifs <;> simp [tanVar]
      rw [e1, e2]; rfl

end Final

end B2

theorem lemma_B2 (D : Formalism.BasicNotions.D7) : PathWeightComponents D :=
  fun _ _ O _ _ _ _ _ _ _ _ _ LL B om hNK hom hpos P c J => B2.kcol_low O LL B om hNK hom hpos P c J

end Formalism.MainNotions.LemmaBAlt
