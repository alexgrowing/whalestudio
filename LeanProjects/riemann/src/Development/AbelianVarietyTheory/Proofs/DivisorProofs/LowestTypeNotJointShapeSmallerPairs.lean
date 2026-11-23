import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.LowestTypeDrop

def rl (S O : List ℚ) (x : ℚ) : ℚ :=
  ((O.countP (fun e => decide (e < x)) : ℚ) - (O.countP (fun e => decide (x < e)) : ℚ)) / 2 -
  ((S.countP (fun e => decide (e < x)) : ℚ) - (S.countP (fun e => decide (x < e)) : ℚ)) / 2

theorem sum_ite_getD (L : List ℚ) (P : ℚ → Prop) [DecidablePred P] :
    (∑ j : Fin L.length, if P (L.getD j 0) then 1 else 0) = L.countP (fun e => decide (P e)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ, List.countP_cons]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ, ih]
    by_cases h : P a <;> simp [h, add_comm]

theorem card_inl (L : List ℚ) {q : ℕ} (P : Ix L.length q → Prop) [DecidablePred P] (Q : ℚ → Prop)
    [DecidablePred Q] (h1 : ∀ j, P (.inl j) ↔ Q (L.getD j 0)) (h2 : ∀ j, ¬ P (.inr j)) :
    (Finset.univ.filter P).card = L.countP (fun e => decide (Q e)) := by
  rw [Finset.card_filter, Fintype.sum_sum_type, ← sum_ite_getD]
  simp [h1, h2]

theorem card_inr (L : List ℚ) {q : ℕ} (P : Ix q L.length → Prop) [DecidablePred P] (Q : ℚ → Prop)
    [DecidablePred Q] (h1 : ∀ j, P (.inr j) ↔ Q (L.getD j 0)) (h2 : ∀ j, ¬ P (.inl j)) :
    (Finset.univ.filter P).card = L.countP (fun e => decide (Q e)) := by
  rw [Finset.card_filter, Fintype.sum_sum_type, ← sum_ite_getD]
  simp [h1, h2]

theorem rhoNC_inl {p q : ℕ} (S O : List ℚ) (hp : S.length = p) (hq : O.length = q) (i : Fin p) :
    rhoNC (ofBlocks (p := p) (q := q) S O) (.inl i) = rl S O (S.getD i 0) := by
  subst hp hq
  unfold rhoNC rl
  rw [card_inr O _ (fun e => e < S.getD i 0), card_inr O _ (fun e => S.getD i 0 < e),
    card_inl S _ (fun e => e < S.getD i 0), card_inl S _ (fun e => S.getD i 0 < e)] <;>
  intro j <;> simp [sameBlock, ofBlocks]

theorem rhoNC_inr {p q : ℕ} (S O : List ℚ) (hp : S.length = p) (hq : O.length = q) (i : Fin q) :
    rhoNC (ofBlocks (p := p) (q := q) S O) (.inr i) = rl O S (O.getD i 0) := by
  subst hp hq
  unfold rhoNC rl
  rw [card_inl S _ (fun e => e < O.getD i 0), card_inl S _ (fun e => O.getD i 0 < e),
    card_inr O _ (fun e => e < O.getD i 0), card_inr O _ (fun e => O.getD i 0 < e)] <;>
  intro j <;> simp [sameBlock, ofBlocks]

theorem count_three (L : List ℚ) (x : ℚ) :
    L.countP (fun e => decide (e < x)) + L.countP (fun e => decide (x < e)) + L.count x = L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.countP_cons, List.count_cons, List.length_cons]
    rcases lt_trichotomy a x with h | h | h
    · simp [h, h.ne, h.not_gt]; omega
    · subst h; simp; omega
    · simp [h, h.ne', h.not_gt]; omega

theorem countP_le_of_image (A : List ℚ) (hA : A.Nodup) (P : ℚ → Bool) (N : ℕ) (φ : ℕ → ℚ)
    (h : ∀ e ∈ A, P e = true → ∃ k < N, e = φ k) : A.countP P ≤ N := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hA.filter _)]
  calc _ ≤ ((Finset.range N).image φ).card := by
        apply Finset.card_le_card
        intro e he
        simp only [List.mem_toFinset, List.mem_filter] at he
        obtain ⟨k, hk, rfl⟩ := h e he.1 he.2
        exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, rfl⟩
    _ ≤ N := by simpa using Finset.card_image_le (s := Finset.range N) (f := φ)

theorem bound_pos (A B C D : List ℚ) (m : ℚ) (hA : A.Nodup) (hAm : ∀ e ∈ A, ∃ k : ℕ, e = m + k)
    (hB : ∀ e ∈ B, e < m) (hD : ∀ e ∈ D, e < m) (x : ℚ) (hx : x ∈ A) :
    m + D.length - B.length + ((A.length : ℚ) + B.length - C.length - D.length - 1) / 2 ≤
      x + rl (A ++ B) (C ++ D) x := by
  obtain ⟨N, hN⟩ := hAm x hx
  have hmx : m ≤ x := by rw [hN]; have : (0 : ℚ) ≤ N := Nat.cast_nonneg N; linarith
  have h1 : A.countP (fun e => decide (e < x)) ≤ N := by
    refine countP_le_of_image A hA _ N (fun k => m + k) fun e he hlt => ?_
    obtain ⟨k, rfl⟩ := hAm e he
    refine ⟨k, ?_, rfl⟩
    have : m + k < m + N := by simpa [hN] using hlt
    exact_mod_cast (show (k : ℚ) < N by linarith)
  have h2 := count_three A x
  have h3 : A.count x ≤ 1 := List.nodup_iff_count_le_one.1 hA x
  have h4 : B.countP (fun e => decide (e < x)) ≤ B.length := List.countP_le_length
  have h5 : D.countP (fun e => decide (e < x)) = D.length :=
    List.countP_eq_length.2 fun e he => by simpa using (hD e he).trans_le hmx
  have h6 : D.countP (fun e => decide (x < e)) = 0 :=
    List.countP_eq_zero.2 fun e he => by simpa using ((hD e he).trans_le hmx).le
  have h7 : C.countP (fun e => decide (x < e)) ≤ C.length := List.countP_le_length
  unfold rl
  simp only [List.countP_append, h5, h6]
  push_cast
  have h1' : ((A.countP (fun e => decide (e < x)) : ℕ) : ℚ) ≤ N := by exact_mod_cast h1
  have h2' : (A.length : ℚ) ≤ (A.countP (fun e => decide (e < x)) : ℕ) +
      (A.countP (fun e => decide (x < e)) : ℕ) + 1 := by exact_mod_cast (by omega)
  have h4' : ((B.countP (fun e => decide (e < x)) : ℕ) : ℚ) ≤ B.length := by exact_mod_cast h4
  have h7' : ((C.countP (fun e => decide (x < e)) : ℕ) : ℚ) ≤ C.length := by exact_mod_cast h7
  have h8 : (0 : ℚ) ≤ (C.countP (fun e => decide (e < x)) : ℕ) := Nat.cast_nonneg _
  have h9 : (0 : ℚ) ≤ (B.countP (fun e => decide (x < e)) : ℕ) := Nat.cast_nonneg _
  linarith

theorem bound_neg (A B C D : List ℚ) (m : ℚ) (hB : B.Nodup) (hBm : ∀ e ∈ B, ∃ k : ℕ, e = -m - k)
    (hA : ∀ e ∈ A, -m < e) (hC : ∀ e ∈ C, -m < e) (x : ℚ) (hx : x ∈ B) :
    x + rl (A ++ B) (C ++ D) x ≤
      -(m + C.length - A.length + ((A.length : ℚ) + B.length - C.length - D.length - 1) / 2) := by
  obtain ⟨N, hN⟩ := hBm x hx
  have hmx : x ≤ -m := by rw [hN]; have : (0 : ℚ) ≤ N := Nat.cast_nonneg N; linarith
  have h1 : B.countP (fun e => decide (x < e)) ≤ N := by
    refine countP_le_of_image B hB _ N (fun k => -m - k) fun e he hlt => ?_
    obtain ⟨k, rfl⟩ := hBm e he
    refine ⟨k, ?_, rfl⟩
    have : -m - N < -m - k := by simpa [hN] using hlt
    exact_mod_cast (show (k : ℚ) < N by linarith)
  have h2 := count_three B x
  have h3 : B.count x ≤ 1 := List.nodup_iff_count_le_one.1 hB x
  have h4 : A.countP (fun e => decide (x < e)) ≤ A.length := List.countP_le_length
  have h5 : C.countP (fun e => decide (x < e)) = C.length :=
    List.countP_eq_length.2 fun e he => by simpa using hmx.trans_lt (hC e he)
  have h6 : C.countP (fun e => decide (e < x)) = 0 :=
    List.countP_eq_zero.2 fun e he => by simpa using (hmx.trans_lt (hC e he)).le
  have h7 : D.countP (fun e => decide (e < x)) ≤ D.length := List.countP_le_length
  unfold rl
  simp only [List.countP_append, h5, h6]
  push_cast
  have h1' : ((B.countP (fun e => decide (x < e)) : ℕ) : ℚ) ≤ N := by exact_mod_cast h1
  have h2' : (B.length : ℚ) ≤ (B.countP (fun e => decide (e < x)) : ℕ) +
      (B.countP (fun e => decide (x < e)) : ℕ) + 1 := by exact_mod_cast (by omega)
  have h4' : ((A.countP (fun e => decide (x < e)) : ℕ) : ℚ) ≤ A.length := by exact_mod_cast h4
  have h7' : ((D.countP (fun e => decide (e < x)) : ℕ) : ℚ) ≤ D.length := by exact_mod_cast h7
  have h8 : (0 : ℚ) ≤ (D.countP (fun e => decide (x < e)) : ℕ) := Nat.cast_nonneg _
  have h9 : (0 : ℚ) ≤ (A.countP (fun e => decide (e < x)) : ℕ) := Nat.cast_nonneg _
  linarith

theorem map_eq_of_getD {n : ℕ} (S T : List ℚ) (F : ℚ → ℚ) (hS : S.length = n) (hT : T.length = n)
    (h : ∀ i : Fin n, F (S.getD i 0) = T.getD i 0) : S.map F = T := by
  apply List.ext_getElem (by simp [hS, hT])
  intro i h1 h2
  have := h ⟨i, hT ▸ h2⟩
  have h3 : i < S.length := by simpa using h1
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, List.getElem?_eq_getElem h3]
    using this

theorem pad_length (a b : List ℤ) (n : ℕ) (h : a.length + b.length ≤ n) :
    (pad a (n - a.length - b.length) b).length = n := by
  simp [pad]; omega

theorem shape_lists {p q : ℕ} (S O T U : List ℚ) (c : ℚ) (hp : S.length = p) (hq : O.length = q)
    (hT : T.length = p) (hU : U.length = q)
    (h : shiftNu c (blattner (ofBlocks (p := p) (q := q) S O)) = ofBlocks T U) :
    S.map (fun x => x + rl S O x - c) = T ∧ O.map (fun x => x + rl O S x + c) = U := by
  constructor
  · refine map_eq_of_getD S T _ hp hT fun i => ?_
    have := congrFun h (.inl i)
    rw [← rhoNC_inl S O hp hq i]
    simpa [shiftNu, blattner, ofBlocks] using this
  · refine map_eq_of_getD O U _ hq hU fun i => ?_
    have := congrFun h (.inr i)
    rw [← rhoNC_inr S O hp hq i]
    simpa [shiftNu, blattner, ofBlocks] using this

theorem len_pos (A B : List ℚ) (F : ℚ → ℚ) (a b : List ℤ) (k : ℕ) (hb : ∀ v ∈ b, v < 0)
    (h : (A ++ B).map F = pad a k b) (hF : ∀ x ∈ A, 0 < F x) : A.length ≤ a.length := by
  have h1 := congrArg (List.countP (fun e : ℚ => decide (0 < e))) h
  simp only [pad, List.map_append, List.countP_append, List.countP_map] at h1
  have h2 : A.countP ((fun e : ℚ => decide (0 < e)) ∘ F) = A.length :=
    List.countP_eq_length.2 fun e he => by simpa using hF e he
  have h3 : b.countP ((fun e : ℚ => decide (0 < e)) ∘ fun v : ℤ => (v : ℚ)) = 0 :=
    List.countP_eq_zero.2 fun e he => by simpa using (hb e he).le
  have h4 : (List.replicate k (0 : ℤ)).countP
      ((fun e : ℚ => decide (0 < e)) ∘ fun v : ℤ => (v : ℚ)) = 0 :=
    List.countP_eq_zero.2 fun e he => by simp [List.eq_of_mem_replicate he]
  have h5 : a.countP ((fun e : ℚ => decide (0 < e)) ∘ fun v : ℤ => (v : ℚ)) ≤ a.length :=
    List.countP_le_length
  omega

theorem len_neg (A B : List ℚ) (F : ℚ → ℚ) (a b : List ℤ) (k : ℕ) (ha : ∀ v ∈ a, 0 < v)
    (h : (A ++ B).map F = pad a k b) (hF : ∀ x ∈ B, F x < 0) : B.length ≤ b.length := by
  have h1 := congrArg (List.countP (fun e : ℚ => decide (e < 0))) h
  simp only [pad, List.map_append, List.countP_append, List.countP_map] at h1
  have h2 : B.countP ((fun e : ℚ => decide (e < 0)) ∘ F) = B.length :=
    List.countP_eq_length.2 fun e he => by simpa using hF e he
  have h3 : a.countP ((fun e : ℚ => decide (e < 0)) ∘ fun v : ℤ => (v : ℚ)) = 0 :=
    List.countP_eq_zero.2 fun e he => by simpa using (ha e he).le
  have h4 : (List.replicate k (0 : ℤ)).countP
      ((fun e : ℚ => decide (e < 0)) ∘ fun v : ℤ => (v : ℚ)) = 0 :=
    List.countP_eq_zero.2 fun e he => by simp [List.eq_of_mem_replicate he]
  have h5 : b.countP ((fun e : ℚ => decide (e < 0)) ∘ fun v : ℤ => (v : ℚ)) ≤ b.length :=
    List.countP_le_length
  omega

theorem cPair_sub (r s i : ℕ) (hr : i ≤ r) (hs : i ≤ s) : cPair (r - i) (s - i) = cPair r s := by
  unfold cPair
  rw [Nat.cast_sub hr, Nat.cast_sub hs]; ring

theorem block_bounds (t : ℕ) : ∀ e ∈ block t, -(((t : ℚ) + 1) / 2) < e ∧ e < ((t : ℚ) + 1) / 2 := by
  intro e he
  have : ∃ k < t, ((t : ℚ) - 1) / 2 - (k : ℕ) = e := by simpa [block] using he
  obtain ⟨k, hk, rfl⟩ := this
  have h1 : (k : ℚ) < t := by exact_mod_cast hk
  have h2 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  constructor <;> linarith

theorem block_length (t : ℕ) : (block t).length = t := by simp [block]

theorem up_coset (m e : ℚ) (hk : ∃ k : ℤ, e = m + k) (h : m ≤ e) : ∃ k : ℕ, e = m + k := by
  obtain ⟨k, rfl⟩ := hk
  have : 0 ≤ k := by exact_mod_cast (show (0 : ℚ) ≤ k by linarith)
  lift k to ℕ using this
  exact ⟨k, by simp⟩

theorem down_coset (t : ℕ) (e : ℚ) (hk : ∃ k : ℤ, e = ((t : ℚ) + 1) / 2 + k)
    (h : e ≤ -(((t : ℚ) + 1) / 2)) : ∃ k : ℕ, e = -(((t : ℚ) + 1) / 2) - k := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨j, hj⟩ := up_coset (((t : ℚ) + 1) / 2) (-e) ⟨-k - t - 1, by rw [hk]; push_cast; ring⟩
    (by linarith)
  exact ⟨j, by linarith⟩

theorem up_strict (m e : ℚ) (hk : ∃ k : ℕ, e = m + k) (h : e ≠ m) : ∃ k : ℕ, e = m + 1 + k := by
  obtain ⟨k, rfl⟩ := hk
  cases k with
  | zero => simp at h
  | succ k => exact ⟨k, by push_cast; ring⟩

theorem down_strict (m e : ℚ) (hk : ∃ k : ℕ, e = -m - k) (h : e ≠ -m) :
    ∃ k : ℕ, e = -(m + 1) - k := by
  obtain ⟨k, rfl⟩ := hk
  cases k with
  | zero => simp at h
  | succ k => exact ⟨k, by push_cast; ring⟩

theorem entry_lamA (al be ga de : List ℚ) (e : ℚ) (he : e ∈ al ++ be ∨ e ∈ ga ++ de) :
    ∃ a, lamA al be ga de a = e := by
  rcases he with he | he
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact ⟨.inl ⟨i, by simpa using hi⟩, by
      simp only [lamA, ofBlocks]; exact List.getD_eq_getElem _ _ hi⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact ⟨.inr ⟨i, by simpa using hi⟩, by
      simp only [lamA, ofBlocks]; exact List.getD_eq_getElem _ _ hi⟩

theorem lowestType_not_jointShape : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → ∀ μ', ¬ JointShape _ _ (al.length + de.length + t - i) (ga.length + be.length - i) (blattner (lamA al be ga de)) μ') ∧ (i ≤ al.length + de.length → i ≤ ga.length + be.length + t → ∀ μ', ¬ JointShape _ _ (al.length + de.length - i) (ga.length + be.length + t - i) (blattner (lamA al be ga de)) μ') ∧ ((¬ (∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2) ∨ ¬ (∃ a, lamA al be ga de a = -(((t : ℚ) + 1) / 2))) → i ≤ al.length + be.length → i ≤ ga.length + de.length → (∀ μ, ¬ JointShape (al.length + be.length - i) (ga.length + de.length - i) _ _ μ (blattner (lamA' t al be ga de))) ∧ ∀ μ, ¬ JointShape (al.length + be.length - i) (ga.length + de.length - i) _ _ μ (blattner (lamM' t al be ga de))) := by
  intro t al be ga de H i hi
  obtain ⟨ht, -, pal, pbe, pga, pde, -, hpos, hneg, hint, habs⟩ := H
  have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have nal : al.Nodup := pal.imp fun h => ne_of_gt h
  have nbe : be.Nodup := pbe.imp fun h => ne_of_gt h
  have nga : ga.Nodup := pga.imp fun h => ne_of_gt h
  have nde : de.Nodup := pde.imp fun h => ne_of_gt h
  have hbl := block_bounds t
  have hbll := block_length t
  have gal : ∀ e ∈ al, ((t : ℚ) + 1) / 2 ≤ e := fun e he => by
    have h1 := habs e (by simp [he]); rwa [abs_of_pos (hpos e (by simp [he]))] at h1
  have gga : ∀ e ∈ ga, ((t : ℚ) + 1) / 2 ≤ e := fun e he => by
    have h1 := habs e (by simp [he]); rwa [abs_of_pos (hpos e (by simp [he]))] at h1
  have gbe : ∀ e ∈ be, e ≤ -(((t : ℚ) + 1) / 2) := fun e he => by
    have h1 := habs e (by simp [he]); rw [abs_of_neg (hneg e (by simp [he]))] at h1; linarith
  have gde : ∀ e ∈ de, e ≤ -(((t : ℚ) + 1) / 2) := fun e he => by
    have h1 := habs e (by simp [he]); rw [abs_of_neg (hneg e (by simp [he]))] at h1; linarith
  have cal := fun e (he : e ∈ al) => up_coset _ e (hint e (by simp [he])) (gal e he)
  have cga := fun e (he : e ∈ ga) => up_coset _ e (hint e (by simp [he])) (gga e he)
  have cbe := fun e (he : e ∈ be) => down_coset t e (hint e (by simp [he])) (gbe e he)
  have cde := fun e (he : e ∈ de) => down_coset t e (hint e (by simp [he])) (gde e he)

  have lal : ∀ m, ((t : ℚ) + 1) / 2 ≤ m → ∀ e ∈ al, -m < e := fun m hm e he => by
    linarith [gal e he]
  have lga : ∀ m, ((t : ℚ) + 1) / 2 ≤ m → ∀ e ∈ ga, -m < e := fun m hm e he => by
    linarith [gga e he]
  have lbe : ∀ m, ((t : ℚ) + 1) / 2 ≤ m → ∀ e ∈ be, e < m := fun m hm e he => by
    linarith [gbe e he]
  have lde : ∀ m, ((t : ℚ) + 1) / 2 ≤ m → ∀ e ∈ de, e < m := fun m hm e he => by
    linarith [gde e he]
  have up : ∀ L : List ℚ, (∀ m, ((t : ℚ) + 1) / 2 ≤ m → ∀ e ∈ L, -m < e) →
      ∀ m, ((t : ℚ) + 1) / 2 ≤ m → ∀ e ∈ L ++ block t, -m < e := fun L hL m hm e he => by
    rcases List.mem_append.1 he with he | he
    · exact hL m hm e he
    · linarith [(hbl e he).1]
  have dn : ∀ L : List ℚ, (∀ m, ((t : ℚ) + 1) / 2 ≤ m → ∀ e ∈ L, e < m) →
      ∀ m, ((t : ℚ) + 1) / 2 ≤ m → ∀ e ∈ block t ++ L, e < m := fun L hL m hm e he => by
    rcases List.mem_append.1 he with he | he
    · linarith [(hbl e he).2]
    · exact hL m hm e he
  have m1 : ((t : ℚ) + 1) / 2 ≤ ((t : ℚ) + 1) / 2 + 1 := by linarith
  refine ⟨fun hr hs μ' hJ => ?_, fun hr hs μ' hJ => ?_, fun hne hp hq => ⟨fun μ hJ => ?_, fun μ hJ => ?_⟩⟩
  · obtain ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, e1, -⟩ := hJ
    rw [cPair_sub _ _ _ hr hs] at e1
    obtain ⟨e2, e3⟩ := shape_lists (al ++ be) (ga ++ de) _ _ _ (by simp) (by simp)
      (pad_length _ _ _ l1) (pad_length _ _ _ l2) e1
    have k1 := len_pos ga de _ _ _ _ hd e3 fun x hx => by
      have := bound_pos ga de al be _ nga cga (lde _ le_rfl) (lbe _ le_rfl) x hx
      simp only [cPair]; push_cast; linarith
    have k2 := len_neg al be _ _ _ _ ha e2 fun x hx => by
      have := bound_neg al be ga de _ nbe cbe (lal _ le_rfl) (lga _ le_rfl) x hx
      simp only [cPair]; push_cast; linarith
    omega
  · obtain ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, e1, -⟩ := hJ
    rw [cPair_sub _ _ _ hr hs] at e1
    obtain ⟨e2, e3⟩ := shape_lists (al ++ be) (ga ++ de) _ _ _ (by simp) (by simp)
      (pad_length _ _ _ l1) (pad_length _ _ _ l2) e1
    have k1 := len_pos al be _ _ _ _ hb e2 fun x hx => by
      have := bound_pos al be ga de _ nal cal (lbe _ le_rfl) (lde _ le_rfl) x hx
      simp only [cPair]; push_cast; linarith
    have k2 := len_neg ga de _ _ _ _ hc e3 fun x hx => by
      have := bound_neg ga de al be _ nde cde (lga _ le_rfl) (lal _ le_rfl) x hx
      simp only [cPair]; push_cast; linarith
    omega
  · obtain ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, -, e1⟩ := hJ
    rw [cPair_sub _ _ _ hp hq] at e1
    obtain ⟨e2, e3⟩ := shape_lists (al ++ block t ++ de) (ga ++ be) _ _ _
      (by simp [hbll]; omega) (by simp) (pad_length _ _ _ l3) (pad_length _ _ _ l4) e1
    rcases hne with hne | hne
    · have k1 := len_neg ga be _ _ _ _ hc e3 fun x hx => by
        have := bound_neg ga be (al ++ block t) de _ nbe cbe (lga _ le_rfl) (up al lal _ le_rfl) x hx
        simp only [cPair, List.length_append, hbll] at this ⊢; push_cast at this ⊢; linarith
      rw [List.append_assoc] at e2
      have k2 := len_pos al (block t ++ de) _ _ _ _ hd e2 fun x hx => by
        have := bound_pos al (block t ++ de) ga be _ nal (fun e he => up_strict _ e (cal e he)
          fun h => hne (h ▸ entry_lamA al be ga de e (by simp [he]))) (dn de lde _ m1) (lbe _ m1) x hx
        simp only [cPair, List.length_append, hbll] at this ⊢; push_cast at this ⊢; linarith
      omega
    · have k2 := len_neg (al ++ block t) de _ _ _ _ ha e2 fun x hx => by
        have := bound_neg (al ++ block t) de ga be _ nde (fun e he => down_strict _ e (cde e he)
          fun h => hne (h ▸ entry_lamA al be ga de e (by simp [he]))) (up al lal _ m1) (lga _ m1) x hx
        simp only [cPair, List.length_append, hbll] at this ⊢; push_cast at this ⊢; linarith
      rw [List.append_assoc] at e3
      have k1 := len_pos ga be _ _ _ _ hb e3 fun x hx => by
        have := bound_pos ga be al (block t ++ de) _ nga cga (lbe _ le_rfl) (dn de lde _ le_rfl) x hx
        simp only [cPair, List.length_append, hbll] at this ⊢; push_cast at this ⊢; linarith
      omega
  · obtain ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, -, e1⟩ := hJ
    rw [cPair_sub _ _ _ hp hq] at e1
    obtain ⟨e2, e3⟩ := shape_lists (al ++ de) (ga ++ block t ++ be) _ _ _
      (by simp) (by simp [hbll]; omega) (pad_length _ _ _ l3) (pad_length _ _ _ l4) e1
    rcases hne with hne | hne
    · have k1 := len_neg al de _ _ _ _ ha e2 fun x hx => by
        have := bound_neg al de (ga ++ block t) be _ nde cde (lal _ le_rfl) (up ga lga _ le_rfl) x hx
        simp only [cPair, List.length_append, hbll] at this ⊢; push_cast at this ⊢; linarith
      rw [List.append_assoc] at e3
      have k2 := len_pos ga (block t ++ be) _ _ _ _ hb e3 fun x hx => by
        have := bound_pos ga (block t ++ be) al de _ nga (fun e he => up_strict _ e (cga e he)
          fun h => hne (h ▸ entry_lamA al be ga de e (by simp [he]))) (dn be lbe _ m1) (lde _ m1) x hx
        simp only [cPair, List.length_append, hbll] at this ⊢; push_cast at this ⊢; linarith
      omega
    · have k2 := len_neg (ga ++ block t) be _ _ _ _ hc e3 fun x hx => by
        have := bound_neg (ga ++ block t) be al de _ nbe (fun e he => down_strict _ e (cbe e he)
          fun h => hne (h ▸ entry_lamA al be ga de e (by simp [he]))) (up ga lga _ m1) (lal _ m1) x hx
        simp only [cPair, List.length_append, hbll] at this ⊢; push_cast at this ⊢; linarith
      rw [List.append_assoc] at e2
      have k1 := len_pos al de _ _ _ _ hd e2 fun x hx => by
        have := bound_pos al de ga (block t ++ be) _ nal cal (lde _ le_rfl) (dn be lbe _ le_rfl) x hx
        simp only [cPair, List.length_append, hbll] at this ⊢; push_cast at this ⊢; linarith
      omega

end GlobalTheory.LowestTypeDrop
