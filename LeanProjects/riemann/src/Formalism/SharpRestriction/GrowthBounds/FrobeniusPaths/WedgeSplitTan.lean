import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColOKOfPath
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

open B2

section Split

variable {r K : ℕ} {P : Type*} [CommRing P]

lemma wedge_split_tan (x : Fin (r + K) → P) (hx : ∀ a : Fin r, x (Fin.castAdd K a) = 0)
    (pl : Finset (Fin r) → P) (tn : Finset (Fin K) → P) (J : Finset (Fin (r + K))) :
    wedgeR x (fun J => pl (Jp J) * tn (Jt J)) J = pl (Jp J) * wedgeR (fun b => x (Fin.natAdd r b)) tn (Jt J) := by
  unfold wedgeR
  rw [sum_split, Finset.sum_eq_zero (fun a _ => by rw [hx]; simp), zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  rw [Jp_erase_na, Jt_erase_na, card_filter_na]; ring

lemma contr_split_tan (x : Fin (r + K) → P) (hx : ∀ a : Fin r, x (Fin.castAdd K a) = 0)
    (pl : Finset (Fin r) → P) (tn : Finset (Fin K) → P) (J : Finset (Fin (r + K))) :
    contrR x (fun J => pl (Jp J) * tn (Jt J)) J = pl (Jp J) * contrR (fun b => x (Fin.natAdd r b)) tn (Jt J) := by
  unfold contrR
  rw [sum_split, Finset.sum_eq_zero (fun a _ => by rw [hx]; simp), zero_add, Finset.mul_sum, Jt_compl]
  refine Finset.sum_congr rfl fun b _ => ?_
  beta_reduce
  rw [Jp_insert_na, Jt_insert_na, card_filter_na]; ring

lemma wedge_split_pl (x : Fin (r + K) → P) (hx : ∀ b : Fin K, x (Fin.natAdd r b) = 0)
    (pl : Finset (Fin r) → P) (tn : Finset (Fin K) → P) (htn : ∀ J'', J'' ≠ ∅ → tn J'' = 0)
    (J : Finset (Fin (r + K))) :
    wedgeR x (fun J => pl (Jp J) * tn (Jt J)) J = wedgeR (fun a => x (Fin.castAdd K a)) pl (Jp J) * tn (Jt J) := by
  unfold wedgeR
  rw [sum_split, Finset.sum_eq_zero (s := Jt J) (fun a _ => by rw [hx]; simp), add_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  beta_reduce
  rw [Jp_erase_ca, Jt_erase_ca, card_filter_ca]
  by_cases h : Jt J = ∅
  · rw [h]; simp only [Finset.card_empty, add_zero]; ring
  · rw [htn _ h]; simp

lemma contr_split_pl (x : Fin (r + K) → P) (hx : ∀ b : Fin K, x (Fin.natAdd r b) = 0)
    (pl : Finset (Fin r) → P) (tn : Finset (Fin K) → P) (htn : ∀ J'', J'' ≠ ∅ → tn J'' = 0)
    (J : Finset (Fin (r + K))) :
    contrR x (fun J => pl (Jp J) * tn (Jt J)) J = contrR (fun a => x (Fin.castAdd K a)) pl (Jp J) * tn (Jt J) := by
  unfold contrR
  rw [sum_split, Finset.sum_eq_zero (s := Jt (univ \ J)) (fun a _ => by rw [hx]; simp), add_zero, Finset.sum_mul,
    Jp_compl]
  refine Finset.sum_congr rfl fun a _ => ?_
  beta_reduce
  rw [Jp_insert_ca, Jt_insert_ca, card_filter_ca]
  by_cases h : Jt J = ∅
  · rw [h]; simp only [Finset.card_empty, add_zero]; ring
  · rw [htn _ h]; simp

end Split

section S2

variable {N r K : ℕ} (R : Type) [CommRing R]

def PLc (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (J' : Finset (Fin r)) :
    MvPolynomial (Fin N × Fin (r + K)) R := rename (plVar (K := K)) (Kcol R (plPart mu) c j J')

def TNc (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (J'' : Finset (Fin K)) :
    MvPolynomial (Fin N × Fin (r + K)) R := rename (tanVar (r := r)) (Kcol R (tanPart mu) c j J'')

lemma PLc_succ (mu : Fin (N + 1) → Fin (r + K) → ℤ) (hdom : ∀ i, Dominant (mu i)) (c : ℤ) (j : ℕ) (h : j < N) :
    PLc R mu c (j + 1) = colStep c (min (colH (mu ⟨j, by omega⟩) c) r) (min (colH (mu ⟨j + 1, by omega⟩) c) r)
      (fun a => X (⟨j, h⟩, Fin.castAdd K a)) (PLc R mu c j) := by
  funext J'
  unfold PLc
  simp only [Kcol, dif_pos h]
  have := colStep_map (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) R →ₐ[R] _).toRingHom c
    (colH (plPart mu ⟨j, by omega⟩) c) (colH (plPart mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩)
    (Kcol R (plPart mu) c j) J'
  refine this.trans ?_
  have e1 : colH (plPart mu ⟨j, by omega⟩) c = min (colH (mu ⟨j, by omega⟩) c) r := colH_pl (hdom _) c
  have e2 : colH (plPart mu ⟨j + 1, by omega⟩) c = min (colH (mu ⟨j + 1, by omega⟩) c) r := colH_pl (hdom _) c
  rw [e1, e2]
  congr 1
  funext a; simp [letVec, plVar]

lemma TNc_succ (mu : Fin (N + 1) → Fin (r + K) → ℤ) (hdom : ∀ i, Dominant (mu i)) (c : ℤ) (j : ℕ) (h : j < N) :
    TNc R mu c (j + 1) = colStep c (colH (mu ⟨j, by omega⟩) c - r) (colH (mu ⟨j + 1, by omega⟩) c - r)
      (fun b => X (⟨j, h⟩, Fin.natAdd r b)) (TNc R mu c j) := by
  funext J'
  unfold TNc
  simp only [Kcol, dif_pos h]
  have := colStep_map (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) R →ₐ[R] _).toRingHom c
    (colH (tanPart mu ⟨j, by omega⟩) c) (colH (tanPart mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩)
    (Kcol R (tanPart mu) c j) J'
  refine this.trans ?_
  have e1 : colH (tanPart mu ⟨j, by omega⟩) c = colH (mu ⟨j, by omega⟩) c - r := colH_tan (hdom _) c
  have e2 : colH (tanPart mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c - r := colH_tan (hdom _) c
  rw [e1, e2]
  congr 1
  funext a; simp [letVec, tanVar]

lemma PLc_zero (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (J' : Finset (Fin r)) :
    PLc R mu c 0 J' = extOne J' :=
  extOne_map (rename (plVar (K := K)) : MvPolynomial (Fin N × Fin r) R →ₐ[R] _).toRingHom J'

lemma TNc_zero (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (J' : Finset (Fin K)) :
    TNc R mu c 0 J' = extOne J' :=
  extOne_map (rename (tanVar (r := r)) : MvPolynomial (Fin N × Fin K) R →ₐ[R] _).toRingHom J'

lemma colStep_same {k : ℕ} {P : Type*} [CommRing P] (c : ℤ) (a b : ℕ) (hab : a = b) (x : Fin k → P)
    (Kv : Finset (Fin k) → P) : colStep c a b x Kv = Kv := by
  subst hab; unfold colStep; simp

lemma TNc_card (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (hdom : ∀ i, Dominant (mu i)) (hc : 1 ≤ c) (j : ℕ) (hj : j ≤ N) :
    ∀ J'', TNc R mu c j J'' ≠ 0 → J''.card = colH (mu ⟨j, by omega⟩) c - r := by
  classical
  induction j with
  | zero =>
    intro J hJ
    rw [TNc_zero] at hJ
    have : J = ∅ := by by_contra hne; exact hJ (by unfold extOne; rw [if_neg hne])
    rw [this, H.start hc]; simp
  | succ j ih =>
    intro J hJ
    have h : j < N := hj
    have ih' := ih (by omega)
    rw [TNc_succ R mu hdom c j h] at hJ
    unfold colStep at hJ
    split_ifs at hJ with h1 h3
    · obtain ⟨_, hN⟩ := H.rise j h (by omega)
      obtain ⟨m, hm, _, hK⟩ := wedgeR_ne _ _ _ hJ
      have := ih' _ hK
      rw [Finset.card_erase_of_mem hm] at this
      have := Finset.card_pos.mpr ⟨m, hm⟩
      omega
    · obtain ⟨_, hP⟩ := H.fall j h (by omega)
      obtain ⟨m, hm, _, hK⟩ := contrR_ne _ _ _ hJ
      have := ih' _ hK
      rw [Finset.card_insert_of_notMem hm] at this
      omega
    · have := ih' _ hJ; omega

lemma condUS_vec (LL : LiftLetters (Fin N)) (i : Fin N) (m : Fin (r + K)) (hv : LL.vec i = true) :
    condUS LL i m ↔ r ≤ m.val := by unfold condUS; simp [hv]

lemma condUS_cov (LL : LiftLetters (Fin N)) (i : Fin N) (m : Fin (r + K)) (hv : LL.vec i = false) :
    condUS LL i m ↔ m.val < r := by unfold condUS; simp [hv]

lemma nomL_X (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (i : Fin N) (m : Fin (r + K))
    (h : condUS LL i m ↔ IsCostly mu c i) : nomL R LL mu c i m = X (i, m) := by
  unfold nomL; rw [if_pos h]

lemma nomL_0 (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (i : Fin N) (m : Fin (r + K))
    (h : ¬ (condUS LL i m ↔ IsCostly mu c i)) : nomL R LL mu c i m = 0 := by
  unfold nomL; rw [if_neg h]

theorem SgW_eq (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (hdom : ∀ i, Dominant (mu i)) (j : ℕ) (hj : j ≤ N) :
    SgW R LL mu c j = fun J => PLc R mu c j (Jp J) * TNc R mu c j (Jt J) := by
  classical
  induction j with
  | zero =>
    funext J
    simp only [SgW, PLc_zero, TNc_zero]
    unfold extOne
    by_cases hJ : J = ∅
    · subst hJ; simp [Jp, Jt]
    · rw [if_neg hJ]
      have := (eq_empty_iff_split J).not.mp hJ
      by_cases h1 : Jp J = ∅
      · rw [if_neg (fun h2 => this ⟨h1, h2⟩)]; simp
      · rw [if_neg h1]; simp
  | succ j ih =>
    have h : j < N := hj
    have ih' := ih (by omega)
    funext J
    simp only [SgW, dif_pos h]
    rw [ih', PLc_succ R mu hdom c j h, TNc_succ R mu hdom c j h]
    have hci := costly_iff mu c j h
    have hca : ∀ a : Fin r, (Fin.castAdd K a).val < r := fun a => by simp
    have hna : ∀ b : Fin K, r ≤ (Fin.natAdd r b).val := fun b => by simp
    have htn0 : 1 ≤ c → colH (mu ⟨j, by omega⟩) c ≤ r → ∀ J'', J'' ≠ ∅ → TNc R mu c j J'' = 0 := by
      intro hc hr J'' hne
      by_contra hh
      have := TNc_card R LL mu c H hdom hc j (by omega) J'' hh
      exact hne (Finset.card_eq_zero.mp (by omega))
    by_cases h1 : colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c
    · obtain ⟨hv, hN⟩ := H.rise j h h1
      have cc : IsCostly mu c ⟨j, h⟩ ↔ r ≤ colH (mu ⟨j, by omega⟩) c := by
        rw [hci]; constructor
        · rintro (⟨_, x⟩ | ⟨x, _⟩) <;> omega
        · intro x; exact Or.inl ⟨h1, x⟩
      by_cases hc : 1 ≤ c
      · by_cases hr : r ≤ colH (mu ⟨j, by omega⟩) c
        · rw [colStep_same c _ _ (by omega) _ (PLc R mu c j)]
          simp only [colStep, if_pos h1, if_pos hc,
            if_pos (show colH (mu ⟨j, by omega⟩) c - r < colH (mu ⟨j + 1, by omega⟩) c - r by omega)]
          rw [wedge_split_tan _ (fun a => nomL_0 R LL mu c _ _ (by
            rw [condUS_vec LL _ _ hv, cc]; have := hca a; intro e; have := e.mpr hr; omega))]
          congr 2
          funext b
          exact nomL_X R LL mu c _ _ (by rw [condUS_vec LL _ _ hv, cc]; exact iff_of_true (hna b) hr)
        · rw [colStep_same c _ _ (by omega) _ (TNc R mu c j)]
          simp only [colStep, if_pos h1, if_pos hc,
            if_pos (show min (colH (mu ⟨j, by omega⟩) c) r < min (colH (mu ⟨j + 1, by omega⟩) c) r by omega)]
          rw [wedge_split_pl _ (fun b => nomL_0 R LL mu c _ _ (by
            rw [condUS_vec LL _ _ hv, cc]; intro e; exact hr (e.mp (hna b)))) _ _ (htn0 hc (by omega))]
          congr 2
          funext a
          exact nomL_X R LL mu c _ _ (by
            rw [condUS_vec LL _ _ hv, cc]; exact iff_of_false (by have := hca a; omega) hr)
      · have hd := H.dual hc j (by omega)
        rw [colStep_same c _ _ (by omega) _ (PLc R mu c j)]
        simp only [colStep, if_pos h1, if_neg hc,
          if_pos (show colH (mu ⟨j, by omega⟩) c - r < colH (mu ⟨j + 1, by omega⟩) c - r by omega)]
        rw [contr_split_tan _ (fun a => nomL_0 R LL mu c _ _ (by
          rw [condUS_vec LL _ _ hv, cc]; have := hca a; intro e; have := e.mpr (by omega); omega))]
        congr 2
        funext b
        exact nomL_X R LL mu c _ _ (by rw [condUS_vec LL _ _ hv, cc]; exact iff_of_true (hna b) (by omega))
    · by_cases h3 : colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c
      · obtain ⟨hv, hP⟩ := H.fall j h h3
        have cc : IsCostly mu c ⟨j, h⟩ ↔ colH (mu ⟨j, by omega⟩) c ≤ r := by
          rw [hci]; constructor
          · rintro (⟨x, _⟩ | ⟨_, x⟩) <;> omega
          · intro x; exact Or.inr ⟨h3, x⟩
        by_cases hc : 1 ≤ c
        · by_cases hr : colH (mu ⟨j, by omega⟩) c ≤ r
          · rw [colStep_same c _ _ (by omega) _ (TNc R mu c j)]
            simp only [colStep, if_neg h1, if_pos h3, if_pos hc,
              if_neg (show ¬ min (colH (mu ⟨j, by omega⟩) c) r < min (colH (mu ⟨j + 1, by omega⟩) c) r by omega),
              if_pos (show min (colH (mu ⟨j + 1, by omega⟩) c) r < min (colH (mu ⟨j, by omega⟩) c) r by omega)]
            rw [contr_split_pl _ (fun b => nomL_0 R LL mu c _ _ (by
              rw [condUS_cov LL _ _ hv, cc]; have := hna b; intro e; have := e.mpr hr; omega)) _ _ (htn0 hc hr)]
            congr 2
            funext a
            exact nomL_X R LL mu c _ _ (by rw [condUS_cov LL _ _ hv, cc]; exact iff_of_true (hca a) hr)
          · rw [colStep_same c _ _ (by omega) _ (PLc R mu c j)]
            simp only [colStep, if_neg h1, if_pos h3, if_pos hc,
              if_neg (show ¬ colH (mu ⟨j, by omega⟩) c - r < colH (mu ⟨j + 1, by omega⟩) c - r by omega),
              if_pos (show colH (mu ⟨j + 1, by omega⟩) c - r < colH (mu ⟨j, by omega⟩) c - r by omega)]
            rw [contr_split_tan _ (fun a => nomL_0 R LL mu c _ _ (by
              rw [condUS_cov LL _ _ hv, cc]; intro e; exact hr (e.mp (hca a))))]
            congr 2
            funext b
            exact nomL_X R LL mu c _ _ (by
              rw [condUS_cov LL _ _ hv, cc]; exact iff_of_false (by have := hna b; omega) hr)
        · have hd := H.dual hc j (by omega)
          have hd' := H.dual hc (j + 1) (by omega)
          rw [colStep_same c _ _ (by omega) _ (PLc R mu c j)]
          simp only [colStep, if_neg h1, if_pos h3, if_neg hc,
            if_neg (show ¬ colH (mu ⟨j, by omega⟩) c - r < colH (mu ⟨j + 1, by omega⟩) c - r by omega),
            if_pos (show colH (mu ⟨j + 1, by omega⟩) c - r < colH (mu ⟨j, by omega⟩) c - r by omega)]
          rw [wedge_split_tan _ (fun a => nomL_0 R LL mu c _ _ (by
            rw [condUS_cov LL _ _ hv, cc]; intro e; have := e.mp (hca a); omega))]
          congr 2
          funext b
          exact nomL_X R LL mu c _ _ (by
            rw [condUS_cov LL _ _ hv, cc]; exact iff_of_false (by have := hna b; omega) (by omega))
      · have e : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c := by omega
        rw [colStep_same c _ _ e, colStep_same c _ _ (by rw [e]), colStep_same c _ _ (by rw [e])]

theorem plTanCol_eq_SgW (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (hdom : ∀ i, Dominant (mu i)) (J : Finset (Fin (r + K))) : plTanCol R mu c J = SgW R LL mu c N J := by
  rw [SgW_eq R LL mu c H hdom N le_rfl]; rfl

end S2

end Formalism.MainNotions.LemmaBAlt
