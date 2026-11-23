import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantVectorMove.SumPermEqSumFirstColumnSplit

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmMove

def extN {n m : ℕ} (b : Fin m → Fin n) (d : Fin n) (k : ℕ) : Fin n :=
  if h : k < m then b ⟨k, h⟩ else d

theorem extN_lt {n m : ℕ} (b : Fin m → Fin n) (d : Fin n) (k : Fin m) : extN b d k = b k := by
  simp [extN, k.isLt]

theorem sgnlem {A : Type*} [Ring A] (z z' : ℤ) (x y : A) :
    ((z * z' : ℤ) : A) * (x * y) = (z : A) * (x * ((z' : A) * y)) := by
  rw [Int.cast_mul, mul_assoc, ← mul_assoc (z' : A) x y, (Int.cast_commute z' x).eq, mul_assoc]

section Cov
variable {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (η : Fin n → A)
  (a : Fin (m + 1) → Fin n) (b : Fin m → Fin n) (w : ℂ)

def Fc (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)) : A :=
  if (q : ℕ) = p then η (a (τ q))
  else Tm E (w - ((q : ℕ) : ℂ)) (a (τ q)) (extN b (a 0) (if (q : ℕ) < p then (q : ℕ) else (q : ℕ) - 1))

def Nc (p : ℕ) : A := ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * (List.ofFn (Fc E η a b w p τ)).prod

omit [Algebra ℂ A] in

def symC (d x c : Fin n) : A := (if x = d then η c else 0) + (if c = d then η x else 0)

theorem midC (hη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0)
    (v v' : ℂ) (hv : v = v' + 1) (x d c : Fin n) :
    η c * Tm E v' x d - Tm E v x d * η c = -symC η d x c := by
  subst hv
  have h := hη x d c
  have hc : η c * algebraMap ℂ A v' = algebraMap ℂ A v' * η c := (Algebra.commutes _ _).symm
  have hk : η c * E x d = E x d * η c - (if c = d then η x else 0) := by
    have e : (if c = d then η x else 0) = (if d = c then η x else 0) := by
      by_cases hcd : c = d
      · rw [if_pos hcd, if_pos hcd.symm]
      · rw [if_neg hcd, if_neg (Ne.symm hcd)]
    rw [e, ← h]
    abel
  simp only [Tm, symC, mul_add, add_mul, hk]
  by_cases hxd : x = d
  · simp only [if_pos hxd]
    rw [hc, map_add, map_one, add_mul, one_mul]
    abel
  · simp only [if_neg hxd, mul_zero, zero_mul, zero_add]
    abel

private lemma list_prod_eq_take_mul_pair_mul_drop {M : Type*} [Monoid M] (l : List M) (i : ℕ) (h : i + 1 < l.length) :
    l.prod = (l.take i).prod * (l[i] * l[i + 1]) * (l.drop (i + 1 + 1)).prod := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero =>
      cases l with
      | nil => simp at h
      | cons y l =>
        rw [List.getElem_cons_succ, List.getElem_cons_zero, List.getElem_cons_zero, List.take_zero,
          List.drop_succ_cons, List.drop_succ_cons, List.drop_zero, List.prod_nil, one_mul,
          List.prod_cons, List.prod_cons, mul_assoc]
    | succ i =>
      have h' : i + 1 < l.length := by simp only [List.length_cons] at h; omega
      rw [List.prod_cons, ih i h', List.take_succ_cons, List.prod_cons, List.getElem_cons_succ,
        List.getElem_cons_succ, List.drop_succ_cons]
      simp only [mul_assoc]

private lemma sum_perm_eq_zero_of_mul_right_eq_neg {B : Type*} [Ring B] [Algebra ℂ B] {k : ℕ} (s : Equiv.Perm (Fin k))
    (G : Equiv.Perm (Fin k) → B) (h : ∀ τ, G (τ * s) = -G τ) : ∑ τ, G τ = 0 := by
  have h1 : ∑ τ, G τ = -∑ τ, G τ := by
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight s)]
    exact Finset.sum_congr rfl fun τ _ => h τ
  have h2 : ∑ τ, G τ + ∑ τ, G τ = 0 := by
    rw [← sub_neg_eq_add, ← h1, sub_self]
  calc ∑ τ, G τ = (2 : ℂ)⁻¹ • ((2 : ℂ) • ∑ τ, G τ) := by
        rw [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]
    _ = 0 := by rw [two_smul, h2, smul_zero]

theorem stepC (hη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0)
    (p : ℕ) (hp : p < m) : Nc E η a b w (p + 1) = -Nc E η a b w p := by
  have hp0 : p < m + 1 := by omega
  have hp1 : p + 1 < m + 1 := by omega
  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin (m + 1)), s = Equiv.swap ⟨p, hp0⟩ ⟨p + 1, hp1⟩ := ⟨_, rfl⟩
  have hne : (⟨p, hp0⟩ : Fin (m + 1)) ≠ ⟨p + 1, hp1⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hsP : s ⟨p, hp0⟩ = ⟨p + 1, hp1⟩ := by rw [hs, Equiv.swap_apply_left]
  have hsP1 : s ⟨p + 1, hp1⟩ = ⟨p, hp0⟩ := by rw [hs, Equiv.swap_apply_right]
  have hsq : ∀ q : Fin (m + 1), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 → s q = q := by
    intro q h1 h2
    rw [hs]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))
  have hsgn : ∀ τ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign (τ * s) : ℤ) : A) = -((Equiv.Perm.sign τ : ℤ) : A) := by
    intro τ
    rw [hs, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, mul_neg_one, Units.val_neg, Int.cast_neg]
  have hoff : ∀ (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fc E η a b w (p + 1) τ q = Fc E η a b w p (τ * s) q := by
    intro τ q h1 h2
    simp only [Fc, Equiv.Perm.mul_apply, hsq q h1 h2, if_neg h1, if_neg h2]
    by_cases hq : (q : ℕ) < p
    · rw [if_pos hq, if_pos (show (q : ℕ) < p + 1 by omega)]
    · rw [if_neg hq, if_neg (show ¬ (q : ℕ) < p + 1 by omega)]
  have hoff2 : ∀ (τ : Equiv.Perm (Fin (m + 1))) (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fc E η a b w (p + 1) (τ * s) q = Fc E η a b w (p + 1) τ q := by
    intro τ q h1 h2
    simp only [Fc, Equiv.Perm.mul_apply, hsq q h1 h2]
  have hT : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w p (τ * s))).take p =
      (List.ofFn (Fc E η a b w (p + 1) τ)).take p := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn] at h1
    exact (hoff τ _ (by show k ≠ p; omega) (by show k ≠ p + 1; omega)).symm
  have hD : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w p (τ * s))).drop (p + 1 + 1) =
      (List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1) := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact (hoff τ _ (by show p + 1 + 1 + k ≠ p; omega) (by show p + 1 + 1 + k ≠ p + 1; omega)).symm
  have hT2 : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w (p + 1) (τ * s))).take p =
      (List.ofFn (Fc E η a b w (p + 1) τ)).take p := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp only [List.length_take, List.length_ofFn] at h1
    exact hoff2 τ _ (by show k ≠ p; omega) (by show k ≠ p + 1; omega)
  have hD2 : ∀ τ : Equiv.Perm (Fin (m + 1)), (List.ofFn (Fc E η a b w (p + 1) (τ * s))).drop (p + 1 + 1) =
      (List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1) := by
    intro τ
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact hoff2 τ _ (by show p + 1 + 1 + k ≠ p; omega) (by show p + 1 + 1 + k ≠ p + 1; omega)
  have e1 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w (p + 1) τ ⟨p, hp0⟩ =
      Tm E (w - (p : ℂ)) (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) := by
    intro τ; simp [Fc]
  have e2 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w (p + 1) τ ⟨p + 1, hp1⟩ =
      η (a (τ ⟨p + 1, hp1⟩)) := by
    intro τ; simp [Fc]
  have e3 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w p (τ * s) ⟨p, hp0⟩ =
      η (a (τ ⟨p + 1, hp1⟩)) := by
    intro τ; simp [Fc, hsP]
  have e4 : ∀ τ : Equiv.Perm (Fin (m + 1)), Fc E η a b w p (τ * s) ⟨p + 1, hp1⟩ =
      Tm E (w - ((p : ℂ) + 1)) (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) := by
    intro τ; simp [Fc, hsP1]
  have key : ∀ τ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn (Fc E η a b w (p + 1) τ)).prod - (List.ofFn (Fc E η a b w p (τ * s))).prod =
        ((List.ofFn (Fc E η a b w (p + 1) τ)).take p).prod *
          symC η (extN b (a 0) p) (a (τ ⟨p, hp0⟩)) (a (τ ⟨p + 1, hp1⟩)) *
          ((List.ofFn (Fc E η a b w (p + 1) τ)).drop (p + 1 + 1)).prod := by
    intro τ
    rw [list_prod_eq_take_mul_pair_mul_drop (List.ofFn (Fc E η a b w (p + 1) τ)) p (by simp; omega),
      list_prod_eq_take_mul_pair_mul_drop (List.ofFn (Fc E η a b w p (τ * s))) p (by simp; omega), hT τ, hD τ,
      ← sub_mul, ← mul_sub]
    congr 2
    simp only [List.getElem_ofFn]
    rw [e1 τ, e2 τ, e3 τ, e4 τ]
    have h := congrArg Neg.neg (midC E η hη (w - (p : ℂ)) (w - ((p : ℂ) + 1)) (by ring)
      (a (τ ⟨p, hp0⟩)) (extN b (a 0) p) (a (τ ⟨p + 1, hp1⟩)))
    rw [neg_sub, neg_neg] at h
    exact h
  have hA : Nc E η a b w p = ∑ τ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign (τ * s) : ℤ) : A) * (List.ofFn (Fc E η a b w p (τ * s))).prod :=
    (Equiv.sum_comp (Equiv.mulRight s)
      (fun τ => ((Equiv.Perm.sign τ : ℤ) : A) * (List.ofFn (Fc E η a b w p τ)).prod)).symm
  rw [hA, Nc]
  simp only [hsgn, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, key]
  apply sum_perm_eq_zero_of_mul_right_eq_neg s
  intro τ
  have hS2 : symC η (extN b (a 0) p) (a ((τ * s) ⟨p, hp0⟩)) (a ((τ * s) ⟨p + 1, hp1⟩)) =
      symC η (extN b (a 0) p) (a (τ ⟨p, hp0⟩)) (a (τ ⟨p + 1, hp1⟩)) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsP, hsP1, symC, symC, add_comm]
  simp only [hsgn, hT2, hD2, hS2, neg_mul]

private lemma sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin {M : Type*} [AddCommMonoid M] {k : ℕ} (π : Equiv.Perm (Fin (k + 1)))
    (F : Equiv.Perm (Fin (k + 1)) → M) :
    ∑ τ, F τ = ∑ j : Fin (k + 1), ∑ σ : Equiv.Perm (Fin k),
      F (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * π) := by
  have hb : Function.Bijective (fun x : Fin (k + 1) × Equiv.Perm (Fin k) =>
      x.1.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, x.2) * π) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [Fintype.card_perm, Nat.factorial_succ]⟩
    rintro ⟨j, σ⟩ ⟨j', σ'⟩ h
    have h1 : j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) =
        j'.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ') := mul_right_cancel h
    have hj : j = j' := by
      have := congrArg (fun e : Equiv.Perm (Fin (k + 1)) => e 0) h1
      simpa [Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero] using this
    subst hj
    have h3 := (Equiv.injective Equiv.Perm.decomposeFin.symm) (mul_left_cancel h1)
    rw [show σ = σ' from congrArg Prod.snd h3]
  rw [← Fintype.sum_prod_type']
  exact (hb.sum_comp F).symm

theorem Nc_zero : Nc E η a b w 0 = ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (η (a j) * qminor E (a ∘ j.succAbove) b (w - 1)) := by
  simp only [Nc, sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin (1 : Equiv.Perm (Fin (m + 1))), mul_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminor, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hs : ((Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ (j : ℕ) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign,
      if_pos rfl, one_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have h0 : Fc E η a b w 0 (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) 0 = η (a j) := by
    simp [Fc, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]
  have h1 : (fun i : Fin m => Fc E η a b w 0 (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ)) i.succ) =
      fun k : Fin m => Tm E (w - 1 - ((k : ℕ) : ℂ)) ((a ∘ j.succAbove) (σ k)) (b k) := by
    funext k
    have hw : w - ((((k : ℕ) + 1 : ℕ)) : ℂ) = w - 1 - ((k : ℕ) : ℂ) := by push_cast; ring
    simp only [Fc, Fin.val_succ, if_neg (Nat.succ_ne_zero _), if_neg (Nat.not_lt_zero _),
      Nat.add_sub_cancel, hw, extN_lt, Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.swap_self, Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply]
  rw [List.ofFn_succ, List.prod_cons, hs, sgnlem, h0, h1]

theorem Nc_last : Nc E η a b w m = ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) * (qminor E (a ∘ j.succAbove) b w * η (a j)) := by
  simp only [Nc, sum_perm_fin_succ_eq_sum_cycleRange_decomposeFin (finRotate (m + 1))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminor, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hjm := j.isLt
  have hu : Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) =
      (-1) ^ (m - (j : ℕ)) * Equiv.Perm.sign σ := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
      Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, sign_finRotate, Nat.add_sub_cancel, mul_right_comm, ← pow_add,
      show (j : ℕ) + m = (m - (j : ℕ)) + 2 * (j : ℕ) by omega, pow_add, pow_mul, Int.units_sq, one_pow,
      mul_one]
  have hs : ((Equiv.Perm.sign (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ (m - (j : ℕ)) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    rw [hu, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have h0 : Fc E η a b w m (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1))
      (Fin.last m) = η (a j) := by
    simp [Fc, finRotate_last, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]
  have h1 : (fun i : Fin m => Fc E η a b w m
      (j.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, σ) * finRotate (m + 1)) i.castSucc) =
      fun k : Fin m => Tm E (w - ((k : ℕ) : ℂ)) ((a ∘ j.succAbove) (σ k)) (b k) := by
    funext k
    have hk := k.isLt
    have hr : finRotate (m + 1) k.castSucc = k.succ := by
      ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last k).ne]
      simp
    simp only [Fc, Fin.coe_castSucc, if_neg (Nat.ne_of_lt hk), if_pos hk, extN_lt, Equiv.Perm.mul_apply, hr,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, Fin.cycleRange_symm_succ,
      Function.comp_apply]
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    hs, h0, h1]
  simp only [Int.cast_mul, mul_assoc]

end Cov

theorem move_operator_covariance : PI.MoveCov := by
  unfold PI.MoveCov
  intro A _ _ n t E η _ hη _ a b w
  have hit : ∀ p, p ≤ t → Nc E η a b w p = (-1 : A) ^ p * Nc E η a b w 0 := by
    intro p
    induction p with
    | zero => intro _; rw [pow_zero, one_mul]
    | succ p ih =>
      intro hp
      rw [stepC E η a b w hη p (by omega), ih (by omega), pow_succ, mul_neg_one, neg_mul]
  have h := hit t le_rfl
  rw [Nc_last, Nc_zero] at h
  have h2 : ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (η (a i) * qminor E (a ∘ i.succAbove) b (w - 1)) =
      (-1 : A) ^ t * ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (t - (j : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ j.succAbove) b w * η (a j)) := by
    rw [h, ← mul_assoc ((-1 : A) ^ t), ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc ((-1 : A) ^ t)]
  congr 1
  have hj := j.isLt
  push_cast
  rw [← pow_add, show t + (t - (j : ℕ)) = (j : ℕ) + 2 * (t - (j : ℕ)) by omega, pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]

end PI.UnitaryGroupMassFormula.QmMove
