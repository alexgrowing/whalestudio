import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section LHwline

variable {K : Type*} [Field K] {r n : ℕ}

def lhwline_rowOp (a b : Fin r) (t : K) (x : Fin r × Fin n → K) : Fin r × Fin n → K :=
  fun v => if v.1 = b then x v + t * x (a, v.2) else x v

def lhwline_colOp (l j : Fin n) (c : K) (x : Fin r × Fin n → K) : Fin r × Fin n → K :=
  fun v => if v.2 = j then x v + c * x (v.1, l) else x v

theorem lhwline_eval_rowGen (a b : Fin r) (t : K) (x : Fin r × Fin n → K)
    (g : MvPolynomial (Fin r × Fin n) K) :
    Polynomial.eval₂ (eval x) t (rowGen K a b g) = eval (lhwline_rowOp a b t x) g := by
  induction g using MvPolynomial.induction_on
  next c =>
    have h1 : rowGen K a b (C c : MvPolynomial (Fin r × Fin n) K) = Polynomial.C (C c) :=
      (rowGen (n := n) K a b).commutes c
    rw [h1, Polynomial.eval₂_C, MvPolynomial.eval_C, MvPolynomial.eval_C]
  next p q hp hq =>
    simp only [map_add, Polynomial.eval₂_add, hp, hq]
  next p v hp =>
    rw [map_mul, Polynomial.eval₂_mul, hp, map_mul]
    congr 1
    simp only [rowGen, aeval_X, eval_X, lhwline_rowOp]
    split_ifs <;> simp <;> ring

theorem lhwline_eval_colAdd (l j : Fin n) (c : K) (x : Fin r × Fin n → K)
    (g : MvPolynomial (Fin r × Fin n) K) :
    eval x (colAdd K l j c g) = eval (lhwline_colOp l j c x) g := by
  induction g using MvPolynomial.induction_on
  next c =>
    simp [colAdd]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp, colAdd, aeval_X, lhwline_colOp]
    congr 1
    split_ifs <;> simp [lhwline_colOp, *]

theorem lhwline_rowDiv_zero (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) K) :
    rowDiv K a b 0 g = g := by
  simp only [rowDiv]
  rw [← Polynomial.constantCoeff_apply]
  induction g using MvPolynomial.induction_on
  next c =>
    have h1 : rowGen K a b (C c : MvPolynomial (Fin r × Fin n) K) = Polynomial.C (C c) :=
      (rowGen (n := n) K a b).commutes c
    rw [h1, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

theorem lhwline_rowGen_eq (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) K)
    (h : ∀ k : ℕ, 1 ≤ k → rowDiv K a b k g = 0) : rowGen K a b g = Polynomial.C g := by
  ext1 k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 := lhwline_rowDiv_zero a b g
    simp only [rowDiv] at h0
    rw [h0, Polynomial.coeff_C_zero]
  · have h1 := h k hk
    simp only [rowDiv] at h1
    rw [h1, Polynomial.coeff_C, if_neg (by omega)]

def lhwline_RInv (φ : (Fin r × Fin n → K) → K) : Prop :=
  ∀ (x : Fin r × Fin n → K) (a b : Fin r) (t : K), a < b → φ (lhwline_rowOp a b t x) = φ x

def lhwline_CInv (φ : (Fin r × Fin n → K) → K) : Prop :=
  ∀ (x : Fin r × Fin n → K) (l j : Fin n) (c : K), l < j → φ (lhwline_colOp l j c x) = φ x

theorem lhwline_RInv_of (g : MvPolynomial (Fin r × Fin n) K)
    (h : ∀ a b : Fin r, a < b → rowGen K a b g = Polynomial.C g) :
    lhwline_RInv (fun x => eval x g) := by
  intro x a b t hab
  show eval (lhwline_rowOp a b t x) g = eval x g
  rw [← lhwline_eval_rowGen, h a b hab, Polynomial.eval₂_C]

theorem lhwline_CInv_of (g : MvPolynomial (Fin r × Fin n) K)
    (h : ∀ l j : Fin n, l < j → ∀ c : K, colAdd K l j c g = g) :
    lhwline_CInv (fun x => eval x g) := by
  intro x l j c hlj
  show eval (lhwline_colOp l j c x) g = eval x g
  rw [← lhwline_eval_colAdd, h l j hlj c]

end LHwline

section LHwlineElim

variable {K : Type*} [Field K] {r n : ℕ}

def lhwline_mrow (p : Fin r) (S : Finset (Fin r)) (t : Fin r → K) (x : Fin r × Fin n → K) :
    Fin r × Fin n → K :=
  fun v => if v.1 ∈ S then x v + t v.1 * x (p, v.2) else x v

def lhwline_mcol (q : Fin n) (S : Finset (Fin n)) (c : Fin n → K) (x : Fin r × Fin n → K) :
    Fin r × Fin n → K :=
  fun v => if v.2 ∈ S then x v + c v.2 * x (v.1, q) else x v

theorem lhwline_mrow_inv (φ : (Fin r × Fin n → K) → K) (hφ : lhwline_RInv φ) (p : Fin r)
    (t : Fin r → K) (x : Fin r × Fin n → K) (S : Finset (Fin r)) (hS : ∀ b ∈ S, p < b) :
    φ (lhwline_mrow p S t x) = φ x := by
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _
    congr 1
  · intro b S hbS ih hS
    have hpS : p ∉ S := fun hp => lt_irrefl p (hS p (Finset.mem_insert_of_mem hp))
    have hpb : p < b := hS b (Finset.mem_insert_self b S)
    have key : lhwline_mrow p (insert b S) t x =
        lhwline_rowOp p b (t b) (lhwline_mrow p S t x) := by
      funext v
      by_cases hv : v.1 = b
      · simp [lhwline_mrow, lhwline_rowOp, hv, hbS, hpS]
      · simp [lhwline_mrow, lhwline_rowOp, hv, hpS]
    rw [key, hφ _ p b (t b) hpb, ih (fun c hc => hS c (Finset.mem_insert_of_mem hc))]

theorem lhwline_mcol_inv (φ : (Fin r × Fin n → K) → K) (hφ : lhwline_CInv φ) (q : Fin n)
    (c : Fin n → K) (x : Fin r × Fin n → K) (S : Finset (Fin n)) (hS : ∀ j ∈ S, q < j) :
    φ (lhwline_mcol q S c x) = φ x := by
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _
    congr 1
  · intro b S hbS ih hS
    have hqS : q ∉ S := fun hq => lt_irrefl q (hS q (Finset.mem_insert_of_mem hq))
    have hqb : q < b := hS b (Finset.mem_insert_self b S)
    have key : lhwline_mcol q (insert b S) c x =
        lhwline_colOp q b (c b) (lhwline_mcol q S c x) := by
      funext v
      by_cases hv : v.2 = b
      · simp [lhwline_mcol, lhwline_colOp, hv, hbS, hqS]
      · simp [lhwline_mcol, lhwline_colOp, hv, hqS]
    rw [key, hφ _ q b (c b) hqb, ih (fun d hd => hS d (Finset.mem_insert_of_mem hd))]

def highestWeightLineUpdate (p : Fin r) (q : Fin n) (x : Fin r × Fin n → K) : Fin r × Fin n → K :=
  let y := lhwline_mrow p (Finset.univ.filter fun b => p < b) (fun b => -(x (b, q) / x (p, q))) x
  lhwline_mcol q (Finset.univ.filter fun j => q < j) (fun j => -(y (p, j) / y (p, q))) y

theorem lhwline_step_inv (φ : (Fin r × Fin n → K) → K) (hR : lhwline_RInv φ) (hC : lhwline_CInv φ)
    (p : Fin r) (q : Fin n) (x : Fin r × Fin n → K) : φ (highestWeightLineUpdate p q x) = φ x := by
  simp only [highestWeightLineUpdate]
  exact (lhwline_mcol_inv φ hC q _ _ _ (fun j hj => (Finset.mem_filter.1 hj).2)).trans
    (lhwline_mrow_inv φ hR p _ x _ (fun b hb => (Finset.mem_filter.1 hb).2))

def lhwline_elim : ℕ → (Fin r × Fin n → K) → (Fin r × Fin n → K)
  | 0, x => x
  | k + 1, x =>
    if h : k < r ∧ k < n then highestWeightLineUpdate ⟨k, h.1⟩ ⟨k, h.2⟩ (lhwline_elim k x)
    else lhwline_elim k x

theorem lhwline_elim_inv (φ : (Fin r × Fin n → K) → K) (hR : lhwline_RInv φ) (hC : lhwline_CInv φ)
    (k : ℕ) (x : Fin r × Fin n → K) : φ (lhwline_elim k x) = φ x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lhwline_elim]
    split_ifs with h
    · rw [lhwline_step_inv φ hR hC, ih]
    · exact ih

def lhwline_cleared (k : ℕ) (x : Fin r × Fin n → K) : Prop :=
  ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → (a.val < k ∨ j.val < k) → x (a, j) = 0

theorem lhwline_step_apply (p : Fin r) (q : Fin n) (x : Fin r × Fin n → K) (a : Fin r) (j : Fin n) :
    highestWeightLineUpdate p q x (a, j) =
      (if p < a then x (a, j) + -(x (a, q) / x (p, q)) * x (p, j) else x (a, j)) +
      (if q < j then -(x (p, j) / x (p, q)) *
        (if p < a then x (a, q) + -(x (a, q) / x (p, q)) * x (p, q) else x (a, q)) else 0) := by
  simp only [highestWeightLineUpdate, lhwline_mcol, lhwline_mrow, Finset.mem_filter, Finset.mem_univ,
    true_and, lt_self_iff_false, if_false]
  split_ifs <;> ring

end LHwlineElim

section LHwlineClear

variable {K : Type} [Field K] {r n : ℕ}

theorem lhwline_step_cleared (k : ℕ) (hr : k < r) (hn : k < n) (y : Fin r × Fin n → K)
    (hy : lhwline_cleared k y) (hp : y (⟨k, hr⟩, ⟨k, hn⟩) ≠ 0) :
    lhwline_cleared (k + 1) (highestWeightLineUpdate ⟨k, hr⟩ ⟨k, hn⟩ y) := by
  intro a j haj hak
  rw [lhwline_step_apply]
  have hkk := hp
  simp only [Fin.lt_def, Fin.val_mk] at haj hak ⊢
  rcases lt_trichotomy a.val k with ha | ha | ha
  · have h1 : y (a, j) = 0 := hy a j haj (Or.inl ha)
    have h2 : y (a, ⟨k, hn⟩) = 0 := hy a ⟨k, hn⟩ (by simp only [Fin.val_mk]; omega) (Or.inl ha)
    simp [show ¬ k < a.val by omega, h1, h2]
  · have ha' : a = ⟨k, hr⟩ := Fin.ext ha
    subst ha'
    simp only [Fin.val_mk] at haj hak ⊢
    rcases lt_or_gt_of_ne (Ne.symm haj) with hj | hj
    · have h1 : y (⟨k, hr⟩, j) = 0 := hy _ j (by simp only [Fin.val_mk]; omega) (Or.inr hj)
      simp [h1, show ¬ k < j.val by omega]
    · simp only [lt_self_iff_false, if_false, if_pos hj]
      field_simp
      ring
  · have hj : j.val ≤ k := by omega
    simp only [if_pos ha, if_neg (show ¬ k < j.val by omega), add_zero]
    rcases lt_or_eq_of_le hj with hj | hj
    · have h1 : y (a, j) = 0 := hy a j haj (Or.inr hj)
      have h2 : y (⟨k, hr⟩, j) = 0 := hy _ j (by simp only [Fin.val_mk]; omega) (Or.inr hj)
      simp [h1, h2]
    · have hj' : j = ⟨k, hn⟩ := Fin.ext hj
      subst hj'
      field_simp
      ring

theorem lhwline_pivot_ne (k : ℕ) (hr : k + 1 ≤ r) (hn : k + 1 ≤ n) (y : Fin r × Fin n → K)
    (hy : lhwline_cleared k y) (hd : eval y (lpMinor K (k + 1) hr hn) ≠ 0) :
    y (⟨k, hr⟩, ⟨k, hn⟩) ≠ 0 := by
  intro h0
  apply hd
  rw [lpMinor, RingHom.map_det]
  refine Matrix.det_eq_zero_of_column_eq_zero (Fin.last k) (fun i => ?_)
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X]
  by_cases hi : i = Fin.last k
  · subst hi
    have e1 : Fin.castLE hr (Fin.last k) = ⟨k, hr⟩ := Fin.ext (by simp)
    have e2 : Fin.castLE hn (Fin.last k) = ⟨k, hn⟩ := Fin.ext (by simp)
    rw [e1, e2]
    exact h0
  · have hik : i.val < k := Fin.val_lt_last hi
    exact hy _ _ (by rw [Fin.coe_castLE, Fin.coe_castLE, Fin.val_last]; omega)
      (Or.inl (by rw [Fin.coe_castLE]; exact hik))

theorem lhwline_minor_RInv (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lhwline_RInv (fun x : Fin r × Fin n → K => eval x (lpMinor K s hr hn)) := by
  intro x a b t hab
  simp only [lpMinor, RingHom.map_det]
  by_cases hb : b.val < s
  · have ha : a.val < s := lt_trans hab hb
    have hne : (⟨b.val, hb⟩ : Fin s) ≠ ⟨a.val, ha⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      exact absurd this (ne_of_gt hab)
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne t)
    congr 1
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.updateRow_apply, lhwline_rowOp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hp : p = ⟨b.val, hb⟩
    · subst hp
      have e1 : Fin.castLE hr (⟨b.val, hb⟩ : Fin s) = b := Fin.ext (by simp)
      have e2 : Fin.castLE hr (⟨a.val, ha⟩ : Fin s) = a := Fin.ext (by simp)
      simp [e1, e2]
    · have hne2 : Fin.castLE hr p ≠ b := by
        intro h
        apply hp
        apply Fin.ext
        have h' := congrArg Fin.val h
        rw [Fin.coe_castLE] at h'
        simpa using h'
      simp [hp, hne2]
  · congr 1
    ext p q
    have hne2 : Fin.castLE hr p ≠ b := by
      intro h
      apply hb
      have h' := congrArg Fin.val h
      rw [Fin.coe_castLE] at h'
      have := p.isLt
      omega
    simp [lhwline_rowOp, hne2]

theorem lhwline_minor_CInv [Infinite K] (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    lhwline_CInv (fun x : Fin r × Fin n → K => eval x (lpMinor K s hr hn)) := by
  intro x l j c hlj
  simp only [lpMinor, RingHom.map_det]
  by_cases hj : j.val < s
  · have hl : l.val < s := lt_trans hlj hj
    have hne : (⟨j.val, hj⟩ : Fin s) ≠ ⟨l.val, hl⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      exact absurd this (ne_of_gt hlj)
    refine Eq.trans ?_ (Matrix.det_updateCol_add_smul_self _ hne c)
    congr 1
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.updateCol_apply, lhwline_colOp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hq : q = ⟨j.val, hj⟩
    · subst hq
      have e1 : Fin.castLE hn (⟨j.val, hj⟩ : Fin s) = j := Fin.ext (by simp)
      have e2 : Fin.castLE hn (⟨l.val, hl⟩ : Fin s) = l := Fin.ext (by simp)
      simp [e1, e2]
    · have hne2 : Fin.castLE hn q ≠ j := by
        intro h
        apply hq
        apply Fin.ext
        have h' := congrArg Fin.val h
        rw [Fin.coe_castLE] at h'
        simpa using h'
      simp [hq, hne2]
  · congr 1
    ext p q
    have hne2 : Fin.castLE hn q ≠ j := by
      intro h
      apply hj
      have h' := congrArg Fin.val h
      rw [Fin.coe_castLE] at h'
      have := q.isLt
      omega
    simp [lhwline_colOp, hne2]

theorem lhwline_elim_cleared [Infinite K] (x : Fin r × Fin n → K)
    (hx : ∀ (s : ℕ) (hr : s + 1 ≤ r) (hn : s + 1 ≤ n), eval x (lpMinor K (s + 1) hr hn) ≠ 0) :
    ∀ k, k ≤ min r n → lhwline_cleared k (lhwline_elim k x) := by
  intro k
  induction k with
  | zero =>
    intro _ a j _ h
    simp at h
  | succ k ih =>
    intro hk
    have hr : k < r := by have := min_le_left r n; omega
    have hn : k < n := by have := min_le_right r n; omega
    have hy := ih (by omega)
    have hel : lhwline_elim (k + 1) x = highestWeightLineUpdate ⟨k, hr⟩ ⟨k, hn⟩ (lhwline_elim k x) := by
      simp only [lhwline_elim]
      rw [dif_pos ⟨hr, hn⟩]
    rw [hel]
    apply lhwline_step_cleared k hr hn _ hy
    apply lhwline_pivot_ne k hr hn _ hy
    have hinv := lhwline_elim_inv (fun z : Fin r × Fin n → K => eval z (lpMinor K (k + 1) hr hn))
      (lhwline_minor_RInv _ _ _) (lhwline_minor_CInv _ _ _) k x
    intro h0
    exact hx k hr hn (hinv.symm.trans h0)

end LHwlineClear

section LHwlineVanish

variable {K : Type} [Field K] {r n : ℕ}

theorem lhwline_elim_offdiag [Infinite K] (x : Fin r × Fin n → K)
    (hx : ∀ (s : ℕ) (hr : s + 1 ≤ r) (hn : s + 1 ≤ n), eval x (lpMinor K (s + 1) hr hn) ≠ 0)
    (a : Fin r) (j : Fin n) (h : a.val ≠ j.val) : lhwline_elim (min r n) x (a, j) = 0 := by
  apply lhwline_elim_cleared x hx (min r n) le_rfl a j h
  rcases le_total r n with hrn | hrn
  · left
    rw [min_eq_left hrn]
    exact a.isLt
  · right
    rw [min_eq_right hrn]
    exact j.isLt

theorem lhwline_vanish [Infinite K] (g : MvPolynomial (Fin r × Fin n) K)
    (hR : ∀ a b : Fin r, a < b → rowGen K a b g = Polynomial.C g)
    (hC : ∀ l j : Fin n, l < j → ∀ c : K, colAdd K l j c g = g)
    (hD : ∀ D : Fin r × Fin n → K,
      (∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0) → eval D g = 0) :
    g = 0 := by
  let I : Fin r × Fin n → K := fun v => if (v.1 : ℕ) = v.2 then 1 else 0
  have hmin : ∀ (s : ℕ) (hr : s ≤ r) (hn : s ≤ n), lpMinor K s hr hn ≠ 0 := by
    intro s hr hn h
    have h2 := congrArg (eval I) h
    rw [map_zero, lpMinor, RingHom.map_det] at h2
    have h3 : (eval I).mapMatrix (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) K)) = 1 := by
      ext p q
      simp [I, Matrix.one_apply, Fin.ext_iff]
    rw [h3, Matrix.det_one] at h2
    exact one_ne_zero h2
  let Q : MvPolynomial (Fin r × Fin n) K := ∏ s : Fin (min r n),
    lpMinor K (s.val + 1) (by have := s.isLt; have := min_le_left r n; omega)
      (by have := s.isLt; have := min_le_right r n; omega)
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun s _ => hmin _ _ _)
  have hgQ : g * Q = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx0 : eval x Q = 0
    · rw [hx0, mul_zero]
    · have hx : ∀ (s : ℕ) (hr : s + 1 ≤ r) (hn : s + 1 ≤ n), eval x (lpMinor K (s + 1) hr hn) ≠ 0 := by
        intro s hr hn
        have hs : s < min r n := lt_min hr hn
        simp only [Q, map_prod] at hx0
        exact (Finset.prod_ne_zero_iff.mp hx0) ⟨s, hs⟩ (Finset.mem_univ _)
      have hinv := lhwline_elim_inv (fun z : Fin r × Fin n → K => eval z g)
        (lhwline_RInv_of g hR) (lhwline_CInv_of g hC) (min r n) x
      rw [show eval x g = eval (lhwline_elim (min r n) x) g from hinv.symm, hD _ (fun a j h => lhwline_elim_offdiag x hx a j h), zero_mul]
  rcases mul_eq_zero.mp hgQ with h | h
  · exact h
  · exact absurd h hQ

theorem lhwline_weight_col (m : Fin r × Fin n →₀ ℕ) (j : Fin n) :
    Finsupp.weight (colW r n) m j = ∑ a : Fin r, m (a, j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  simp [colW, Pi.single_apply]

theorem lhwline_diag_tall (ν : Fin n → ℕ) (s : Fin n) (hs : r ≤ s.val) (hνs : 0 < ν s)
    (g : MvPolynomial (Fin r × Fin n) K) (hg : IsWeightedHomogeneous (colW r n) g ν)
    (D : Fin r × Fin n → K) (hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0) :
    eval D g = 0 := by
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_eq_zero
  intro m hm
  have hw : Finsupp.weight (colW r n) m = ν := hg (mem_support_iff.mp hm)
  have hcol : ∑ a : Fin r, m (a, s) ≠ 0 := by
    rw [← lhwline_weight_col, hw]
    exact Nat.pos_iff_ne_zero.mp hνs
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcol
  have hDa : D (a, s) = 0 := hD a s (by have := a.isLt; omega)
  rw [Finset.prod_eq_zero (Finset.mem_univ (a, s)) (by rw [hDa, zero_pow ha]), mul_zero]

def lhwline_mnu (hn : n ≤ r) (ν : Fin n → ℕ) : Fin r × Fin n →₀ ℕ :=
  ∑ j : Fin n, Finsupp.single (Fin.castLE hn j, j) (ν j)

theorem lhwline_mnu_apply (hn : n ≤ r) (ν : Fin n → ℕ) (a : Fin r) (j : Fin n) :
    lhwline_mnu hn ν (a, j) = if a.val = j.val then ν j else 0 := by
  simp only [lhwline_mnu, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single j]
  · by_cases h : a.val = j.val
    · have : Fin.castLE hn j = a := Fin.ext (by rw [Fin.coe_castLE]; exact h.symm)
      simp [this, h]
    · have : ¬ (Fin.castLE hn j, j) = (a, j) := by
        intro h'
        apply h
        rw [← (Prod.mk.inj h').1, Fin.coe_castLE]
      simp [this, h]
  · intro b _ hb
    rw [if_neg]
    intro h'
    exact hb (Prod.mk.inj h').2
  · simp

theorem lhwline_mono_zero (hn : n ≤ r) (ν : Fin n → ℕ)
    (g : MvPolynomial (Fin r × Fin n) K) (hg : IsWeightedHomogeneous (colW r n) g ν)
    (D : Fin r × Fin n → K) (hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0)
    (m : Fin r × Fin n →₀ ℕ) (hm : m ∈ g.support) (hne : m ≠ lhwline_mnu hn ν) :
    ∏ v, D v ^ m v = 0 := by
  by_contra hprod
  apply hne
  have hoff : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → m (a, j) = 0 := by
    intro a j h
    by_contra hm0
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ (a, j)) (by rw [hD a j h, zero_pow hm0]))
  have hw : Finsupp.weight (colW r n) m = ν := hg (mem_support_iff.mp hm)
  ext ⟨a, j⟩
  rw [lhwline_mnu_apply]
  split_ifs with h
  · have hc := congrFun hw j
    rw [lhwline_weight_col, Finset.sum_eq_single a] at hc
    · exact hc
    · intro b _ hb
      exact hoff b j (by intro hbj; exact hb (Fin.ext (by omega)))
    · simp
  · exact hoff a j h

theorem lhwline_diag (hn : n ≤ r) (ν : Fin n → ℕ)
    (g : MvPolynomial (Fin r × Fin n) K) (hg : IsWeightedHomogeneous (colW r n) g ν)
    (D : Fin r × Fin n → K) (hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0) :
    eval D g = coeff (lhwline_mnu hn ν) g * ∏ v, D v ^ (lhwline_mnu hn ν) v := by
  rw [MvPolynomial.eval_eq', Finset.sum_eq_single (lhwline_mnu hn ν)]
  · intro m hm hne
    rw [lhwline_mono_zero hn ν g hg D hD m hm hne, mul_zero]
  · intro h
    simp only [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul]

end LHwlineVanish

end Formalism.GradedWeylDivisibility
