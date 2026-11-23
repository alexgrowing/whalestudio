import Mathlib
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

noncomputable section

namespace PI.QnZeroLevelWork

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  rcases Nat.lt_or_ge k.val p.val with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h), if_pos h]
    simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using h), if_neg (by omega)]
    simp

theorem skip_one_eq_succAbove {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : skip1 i j = i.succAbove j := by
  apply Fin.ext
  rw [val_succAbove]
  unfold skip1
  split_ifs <;> simp_all

theorem skip_two_succAbove_comp_alt {t : ℕ} (i : Fin (t + 2)) (i' : Fin (t + 1)) (j : Fin t) (hii : i.val ≤ i'.val) :
    skip2 i (i.succAbove i') j = i.succAbove (i'.succAbove j) := by
  have hv : (i.succAbove i').val = i'.val + 1 := by
    rw [val_succAbove]; split_ifs <;> omega
  apply Fin.ext
  rw [val_succAbove, val_succAbove]
  unfold skip2
  split_ifs <;> simp_all <;> omega

theorem skipSucc : SkipSucc := fun _ i j => skip_one_eq_succAbove i j

theorem skipSucc2 : SkipSucc2 := fun _ i i' j h => skip_two_succAbove_comp_alt i i' j h

theorem capLZero : CapLZero := by
  intro E _ _ k r u f
  rfl

theorem pair_sum {M : Type*} [AddCommMonoid M] {n : ℕ} (i : Fin (n + 2)) (G : Fin (n + 2) → M) :
    (∑ i' : Fin (n + 2), if i < i' then G i' else 0) =
      ∑ i'' : Fin (n + 1), if (i : ℕ) ≤ (i'' : ℕ) then G (i.succAbove i'') else 0 := by
  rw [Fin.sum_univ_succAbove _ i, if_neg (lt_irrefl i), zero_add]
  refine sum_congr rfl fun i'' _ => ?_
  have h : i < i.succAbove i'' ↔ (i : ℕ) ≤ (i'' : ℕ) := by
    rw [Fin.lt_def, val_succAbove]; split_ifs <;> omega
  simp only [h]

theorem quad_sum {M : Type*} [AddCommMonoid M] {n : ℕ}
    (T : Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → M) :
    (∑ i : Fin (n + 2), ∑ i' : Fin (n + 2), ∑ j : Fin (n + 2), ∑ j' : Fin (n + 2),
      if i < i' ∧ j < j' then T i i' j j' else 0) =
    ∑ i : Fin (n + 2), ∑ i'' : Fin (n + 1), ∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
      if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0 := by
  refine sum_congr rfl fun i _ => ?_
  have h1 : ∀ i' : Fin (n + 2), (∑ j : Fin (n + 2), ∑ j' : Fin (n + 2),
      if i < i' ∧ j < j' then T i i' j j' else 0) =
      if i < i' then ∑ j : Fin (n + 2), ∑ j' : Fin (n + 2), (if j < j' then T i i' j j' else 0) else 0 := by
    intro i'; by_cases h : i < i' <;> simp [h]
  have h2 : ∀ i'' : Fin (n + 1), (∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
      if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0) =
      if (i : ℕ) ≤ (i'' : ℕ) then ∑ j : Fin (n + 2), ∑ j'' : Fin (n + 1),
        (if (j : ℕ) ≤ (j'' : ℕ) then T i (i.succAbove i'') j (j.succAbove j'') else 0) else 0 := by
    intro i''; by_cases h : (i : ℕ) ≤ (i'' : ℕ) <;> simp [h]
  simp only [h1, h2]
  rw [pair_sum i]
  refine sum_congr rfl fun i'' _ => ?_
  split_ifs
  · exact sum_congr rfl fun j _ => pair_sum j (fun j' => T i (i.succAbove i'') j j')
  · rfl

section Ops

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}

theorem qm_congr {n t : ℕ}
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (a a' b b' : Fin t → Fin n) (ha : a = a') (hb : b = b') (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    qminorOp Eop a b u f = qminorOp Eop a' b' u f := by
  subst ha hb
  rfl

theorem comp1 (i : Fin (2 * r + k + 2)) :
    (posL (k + 1) r 0 ∘ skip1 i : Fin (2 * r + k + 2 - 1) → Fin (2 * r + (k + 1) + 1)) = i.succAbove := by
  funext j
  exact skip_one_eq_succAbove i j

theorem comp2 (i : Fin (2 * r + k + 2)) (i'' : Fin (2 * r + k + 1)) (h : (i : ℕ) ≤ (i'' : ℕ)) :
    (posL (k + 1) r 0 ∘ skip2 i (i.succAbove i'') : Fin (2 * r + k + 2 - 2) → Fin (2 * r + (k + 1) + 1)) =
      drop2 i i'' := by
  funext j
  exact skip_two_succAbove_comp_alt i i'' j h

def T1 (u : ℂ) (a β : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E) (g : Mx (k + 1) r)
    (i j : Fin (2 * r + k + 2)) : E :=
  ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * β g i * a g j) •
    qminorOp (EH (k + 1) r) (posL (k + 1) r 0 ∘ skip1 i) (posL (k + 1) r 0 ∘ skip1 j) u f g

def T2 (u : ℂ) (a a' β β' : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E)
    (g : Mx (k + 1) r) (i i' j j' : Fin (2 * r + k + 2)) : E :=
  ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β g i * β' g i' - β g i' * β' g i) *
    (a g j * a' g j' - a g j' * a' g j)) •
    qminorOp (EH (k + 1) r) (posL (k + 1) r 0 ∘ skip2 i i') (posL (k + 1) r 0 ∘ skip2 j j') u f g

theorem chat_eq' (u : ℂ) (a β : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E) :
    chatL (EH (k + 1) r) (posL (k + 1) r 0) u a β f =
      chatOp (m := 2 * r + k + 1) (EabH (Hpk (k + 1) r)) u a β f := by
  funext g
  calc chatL (EH (k + 1) r) (posL (k + 1) r 0) u a β f g
      = ∑ i : Fin (2 * r + k + 2), ∑ j : Fin (2 * r + k + 2), T1 u a β f g i j := rfl
    _ = chatOp (m := 2 * r + k + 1) (EabH (Hpk (k + 1) r)) u a β f g := by
      unfold chatOp minorOp
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      exact congrArg (((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * β g i * a g j) • ·)
        (congrFun (qm_congr (EH (k + 1) r) _ _ _ _ (comp1 i) (comp1 j) u f) g)

theorem second_minor_zero_level_formula (u : ℂ) (a a' β β' : Mx (k + 1) r → Fin (2 * r + k + 2) → ℂ) (f : Mx (k + 1) r → E) :
    chat2L (EH (k + 1) r) (posL (k + 1) r 0) u a a' β β' f =
      chat2Op (m := 2 * r + k) (EabH (Hpk (k + 1) r)) u a a' β β' f := by
  funext g
  calc chat2L (EH (k + 1) r) (posL (k + 1) r 0) u a a' β β' f g
      = ∑ i : Fin (2 * r + k + 2), ∑ i' : Fin (2 * r + k + 2), ∑ j : Fin (2 * r + k + 2),
          ∑ j' : Fin (2 * r + k + 2),
          (if i < i' ∧ j < j' then T2 u a a' β β' f g i i' j j' else 0) := rfl
    _ = ∑ i : Fin (2 * r + k + 2), ∑ i'' : Fin (2 * r + k + 1), ∑ j : Fin (2 * r + k + 2),
          ∑ j'' : Fin (2 * r + k + 1),
          (if (i : ℕ) ≤ (i'' : ℕ) ∧ (j : ℕ) ≤ (j'' : ℕ) then
            T2 u a a' β β' f g i (i.succAbove i'') j (j.succAbove j'') else 0) := quad_sum _
    _ = chat2Op (m := 2 * r + k) (EabH (Hpk (k + 1) r)) u a a' β β' f g := by
      unfold chat2Op minor2Op
      refine sum_congr rfl fun i _ => sum_congr rfl fun i'' _ => sum_congr rfl fun j _ =>
        sum_congr rfl fun j'' _ => ?_
      split_ifs with h
      · exact congrArg (((-1 : ℂ) ^ ((i : ℕ) + (i.succAbove i'' : ℕ) + (j : ℕ) + (j.succAbove j'' : ℕ)) *
            (β g i * β' g (i.succAbove i'') - β g (i.succAbove i'') * β' g i) *
            (a g j * a' g (j.succAbove j'') - a g (j.succAbove j'') * a' g j)) • ·)
          (congrFun (qm_congr (EH (k + 1) r) _ _ _ _ (comp2 i i'' h.1) (comp2 j j'' h.2) u f) g)
      · rfl

theorem chat_eq (u : ℂ) (a β : Mx (k + 1) r → Fin (mdim (k + 1) r 0) → ℂ) (f : Mx (k + 1) r → E) :
    chatL (EH (k + 1) r) (posL (k + 1) r 0) u a β f =
      chatOp (m := 2 * r + k + 1) (EabH (Hpk (k + 1) r)) u a β f :=
  chat_eq' u a β f

theorem second_minor_zero_level (u : ℂ) (a a' β β' : Mx (k + 1) r → Fin (mdim (k + 1) r 0) → ℂ) (f : Mx (k + 1) r → E) :
    chat2L (EH (k + 1) r) (posL (k + 1) r 0) u a a' β β' f =
      chat2Op (m := 2 * r + k) (EabH (Hpk (k + 1) r)) u a a' β β' f :=
  second_minor_zero_level_formula u a a' β β' f

theorem uC_eq (k r : ℕ) (Y : ℂ) :
    uC (k + 1) r 0 Y = Y + (((2 * r + (k + 1) + 1 : ℕ) : ℂ) / 2 - 1 / 2) := by
  simp only [uC, mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring

end Ops

theorem tLZero : TLZero := by
  intro E _ _ k r z z' Y p q f
  have hu := uC_eq k r Y
  fin_cases p <;> fin_cases q
  · show capL (k + 1) r 0 (uC (k + 1) r 0 Y) f = _
    rw [hu]
    rfl
  · show -(chatL (EH (k + 1) r) (posL (k + 1) r 0) (uC (k + 1) r 0 Y - 1) (fun _ => xv (k + 1) r z' 0)
      (ybv (k + 1) r z 0) f) = _
    rw [hu, chat_eq]
    rfl
  · show -(chatL (EH (k + 1) r) (posL (k + 1) r 0) (uC (k + 1) r 0 Y) (yv (k + 1) r z 0)
      (fun _ => xbv (k + 1) r z' 0) f) = _
    rw [hu, chat_eq]
    rfl
  · show -(chat2L (EH (k + 1) r) (posL (k + 1) r 0) (uC (k + 1) r 0 Y - 1) (yv (k + 1) r z 0)
      (fun _ => xv (k + 1) r z' 0) (ybv (k + 1) r z 0) (fun _ => xbv (k + 1) r z' 0) f) = _
    rw [hu, second_minor_zero_level]
    rfl

theorem qnZeroLevel : CapLZero ∧ TLZero := ⟨capLZero, tLZero⟩

end PI.QnZeroLevelWork
