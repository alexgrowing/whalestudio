import Mathlib

noncomputable section

namespace PositivityTheory.KB.ChainCochainPairing

variable {Y : Type}

def cob {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : (Fin (m + 2) → Y) → ℝ :=
  fun y => ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F fun j => y (i.succAbove j)

def pr : (n : ℕ) → ((Fin (n + 1) → Y) → ℝ) → (Fin n → Y) → (Fin n → Y) → ℝ
  | 0, _, _, _ => 0
  | n + 1, F, a, b => F (Fin.cons (a 0) b) - pr n (fun x => F (Fin.cons (a 0) x)) (Fin.tail a) (Fin.tail b)

theorem pr_sub (n : ℕ) (F F' : (Fin (n + 1) → Y) → ℝ) (a b : Fin n → Y) :
    pr n (fun x => F x - F' x) a b = pr n F a b - pr n F' a b := by
  induction n with
  | zero => simp [pr]
  | succ n ih =>
    simp only [pr]
    rw [ih]
    ring

theorem pr_zero (n : ℕ) (a b : Fin n → Y) : pr n (fun _ => 0) a b = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pr, ih, sub_zero]

theorem cons_smul {H : Type} [Monoid H] [MulAction H Y] {n : ℕ} (h : H) (v : Y) (x : Fin n → Y) :
    (Fin.cons (h • v) (fun j => h • x j) : Fin (n + 1) → Y) = fun j => h • (Fin.cons v x : Fin (n + 1) → Y) j := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem pr_smul {H : Type} [Monoid H] [MulAction H Y] (h : H) (n : ℕ) (F F' : (Fin (n + 1) → Y) → ℝ)
    (hF : ∀ x, F (fun j => h • x j) = F' x) (a b : Fin n → Y) :
    pr n F (fun j => h • a j) (fun j => h • b j) = pr n F' a b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pr]
    rw [cons_smul, hF]
    congr 1
    exact ih (fun x => F (Fin.cons (h • a 0) x)) (fun x => F' (Fin.cons (a 0) x))
      (fun x => by rw [cons_smul, hF]) (Fin.tail a) (Fin.tail b)

theorem cons_succAbove_succ {n : ℕ} (v : Y) (x : Fin (n + 1) → Y) (i : Fin (n + 1)) :
    (fun j : Fin (n + 1) => (Fin.cons v x : Fin (n + 2) → Y) ((Fin.succ i).succAbove j)) =
      Fin.cons v fun j => x (i.succAbove j) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.succ_succAbove_succ]

theorem succAbove_succ_eq_cons {n : ℕ} (a : Fin (n + 2) → Y) (i : Fin (n + 1)) :
    (fun j : Fin (n + 1) => a ((Fin.succ i).succAbove j)) =
      Fin.cons (a 0) fun j => Fin.tail a (i.succAbove j) := by
  conv_lhs => rw [← Fin.cons_self_tail a]
  exact cons_succAbove_succ _ _ _

theorem cob_cons {m : ℕ} (F : (Fin (m + 2) → Y) → ℝ) (v : Y) (x : Fin (m + 2) → Y) :
    cob F (Fin.cons v x) = F x - cob (fun u => F (Fin.cons v u)) x := by
  unfold cob
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ, cons_succAbove_succ]
  have h0 : (fun j : Fin (m + 2) => (Fin.cons v x : Fin (m + 3) → Y) ((0 : Fin (m + 3)).succAbove j)) = x := by
    funext j; simp
  rw [h0, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem prism (n : ℕ) (F : (Fin (n + 1) → Y) → ℝ) (a b : Fin (n + 1) → Y) :
    pr (n + 1) (cob F) a b +
        ∑ l : Fin (n + 1), (-1 : ℝ) ^ (l : ℕ) * pr n F (fun j => a (l.succAbove j)) (fun j => b (l.succAbove j)) =
      F b - F a := by
  induction n with
  | zero =>
    have h0 : (fun j : Fin 1 => (Fin.cons (a 0) b : Fin 2 → Y) ((0 : Fin 2).succAbove j)) = b := by
      funext j; simp
    have h1 : (fun j : Fin 1 => (Fin.cons (a 0) b : Fin 2 → Y) ((1 : Fin 2).succAbove j)) = a := by
      funext j; fin_cases j; rfl
    show cob F (Fin.cons (a 0) b) - 0 + ∑ l : Fin 1, (-1 : ℝ) ^ (l : ℕ) * 0 = F b - F a
    unfold cob
    rw [Fin.sum_univ_two, h0, h1]
    simp
    ring
  | succ n ih =>
    set v := a 0
    set Fv : (Fin (n + 1) → Y) → ℝ := fun u => F (Fin.cons v u) with hFv
    set S1 := ∑ l : Fin (n + 1), (-1 : ℝ) ^ (l : ℕ) *
      pr n Fv (fun j => Fin.tail a (l.succAbove j)) (fun j => Fin.tail b (l.succAbove j))
    set S2 := ∑ l : Fin (n + 1), (-1 : ℝ) ^ (l : ℕ) * Fv (fun j => b ((Fin.succ l).succAbove j))
    have hterm : ∀ l : Fin (n + 1),
        (-1 : ℝ) ^ ((Fin.succ l : Fin (n + 2)) : ℕ) *
            pr (n + 1) F (fun j => a ((Fin.succ l).succAbove j)) (fun j => b ((Fin.succ l).succAbove j)) =
          (-1 : ℝ) ^ (l : ℕ) * pr n Fv (fun j => Fin.tail a (l.succAbove j)) (fun j => Fin.tail b (l.succAbove j)) -
            (-1 : ℝ) ^ (l : ℕ) * Fv (fun j => b ((Fin.succ l).succAbove j)) := by
      intro l
      rw [succAbove_succ_eq_cons a l]
      have ht : Fin.tail (fun j => b ((Fin.succ l).succAbove j)) = fun j => Fin.tail b (l.succAbove j) := by
        funext j; simp [Fin.tail, Fin.succ_succAbove_succ]
      simp only [pr, Fin.cons_zero, Fin.tail_cons, ht, Fin.val_succ, pow_succ]
      ring
    have hsum : ∑ l : Fin (n + 2), (-1 : ℝ) ^ (l : ℕ) *
          pr (n + 1) F (fun j => a (l.succAbove j)) (fun j => b (l.succAbove j)) =
        pr (n + 1) F (Fin.tail a) (Fin.tail b) + S1 - S2 := by
      rw [Fin.sum_univ_succ]
      simp only [hterm, Finset.sum_sub_distrib, Fin.val_zero, pow_zero, one_mul]
      rw [add_sub_assoc]
      rfl
    have hcob : cob Fv b = Fv (Fin.tail b) - S2 := by
      unfold cob
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hcone : cob F (Fin.cons v b) = F b - cob Fv b := cob_cons F v b
    have hpr : pr (n + 1) (fun x => cob F (Fin.cons v x)) (Fin.tail a) (Fin.tail b) =
        pr (n + 1) F (Fin.tail a) (Fin.tail b) - pr (n + 1) (cob Fv) (Fin.tail a) (Fin.tail b) := by
      rw [← pr_sub]
      congr 1
      funext x
      exact cob_cons F v x
    have hFa : Fv (Fin.tail a) = F a := by
      simp only [hFv, v, Fin.cons_self_tail]
    have ih' := ih Fv (Fin.tail a) (Fin.tail b)
    show cob F (Fin.cons v b) - pr (n + 1) (fun x => cob F (Fin.cons v x)) (Fin.tail a) (Fin.tail b) + _ = _
    rw [hsum, hcone, hpr]
    linarith

end PositivityTheory.KB.ChainCochainPairing
