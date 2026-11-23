import Formalism.RealPlaceAnalysis.StatementE

open Finset

noncomputable section

namespace Formalism.REAL

private theorem update_zero_apply_zero {A : Type*} {t : ℕ} (F : Fin (t + 1) → A) (x : A) :
    Function.update F 0 x 0 = x := by
  rw [Function.update_apply, if_pos rfl]

private theorem update_zero_comp_succ {A : Type*} {t : ℕ} (F : Fin (t + 1) → A) (x : A) :
    (fun i : Fin t => Function.update F 0 x i.succ) = fun i => F i.succ := by
  funext i
  rw [Function.update_apply, if_neg (Fin.succ_ne_zero i)]

private theorem update_succ_apply_zero {A : Type*} {t : ℕ} (F : Fin (t + 1) → A) (j : Fin t) (x : A) :
    Function.update F j.succ x 0 = F 0 := by
  rw [Function.update_apply, if_neg (Fin.succ_ne_zero j).symm]

private theorem update_succ_comp_succ {A : Type*} {t : ℕ} (F : Fin (t + 1) → A) (j : Fin t) (x : A) :
    (fun i : Fin t => Function.update F j.succ x i.succ) = Function.update (fun i => F i.succ) j x := by
  funext i
  rw [Function.update_apply, Function.update_apply]
  simp only [Fin.succ_inj]

private theorem prod_ofFn_update_zero {A : Type*} [Monoid A] {t : ℕ} (F : Fin (t + 1) → A) (x : A) :
    (List.ofFn (Function.update F 0 x)).prod = x * (List.ofFn fun i : Fin t => F i.succ).prod := by
  rw [List.ofFn_succ, List.prod_cons, update_zero_apply_zero, update_zero_comp_succ]

private theorem prod_ofFn_update_succ {A : Type*} [Monoid A] {t : ℕ} (F : Fin (t + 1) → A) (j : Fin t) (x : A) :
    (List.ofFn (Function.update F j.succ x)).prod =
      F 0 * (List.ofFn (Function.update (fun i : Fin t => F i.succ) j x)).prod := by
  rw [List.ofFn_succ, List.prod_cons, update_succ_apply_zero, update_succ_comp_succ]

theorem prod_ofFn_update_eq_mul {A : Type*} [Ring A] : ∀ {t : ℕ} (F : Fin t → A) (k : Fin t),
    ∃ L R : A, ∀ x : A, (List.ofFn (Function.update F k x)).prod = L * x * R
  | 0, _, k => k.elim0
  | t + 1, F, k => by
    refine Fin.cases ?_ (fun k' => ?_) k
    · refine ⟨1, (List.ofFn fun i : Fin t => F i.succ).prod, fun x => ?_⟩
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    · obtain ⟨L, R, h⟩ := prod_ofFn_update_eq_mul (fun i : Fin t => F i.succ) k'
      refine ⟨F 0 * L, R, fun x => ?_⟩
      have hf : (fun i : Fin t => Function.update F k'.succ x i.succ) =
          Function.update (fun i : Fin t => F i.succ) k' x := by
        funext i; simp [Function.update_apply, Fin.succ_inj]
      rw [List.ofFn_succ, List.prod_cons, hf, h]
      simp [Function.update_apply, (Fin.succ_ne_zero k').symm, mul_assoc]

theorem prod_ofFn_update_sub {A : Type*} [Ring A] {t : ℕ} (F : Fin t → A) (k : Fin t) (x y : A) :
    (List.ofFn (Function.update F k (x - y))).prod =
      (List.ofFn (Function.update F k x)).prod - (List.ofFn (Function.update F k y)).prod := by
  obtain ⟨L, R, h⟩ := prod_ofFn_update_eq_mul F k
  rw [h, h, h, mul_sub, sub_mul]

theorem prod_ofFn_update_ite {A : Type*} [Ring A] {t : ℕ} (F : Fin t → A) (k : Fin t) (p : Prop)
    [Decidable p] (x : A) :
    (List.ofFn (Function.update F k (if p then x else 0))).prod =
      if p then (List.ofFn (Function.update F k x)).prod else 0 := by
  by_cases hp : p
  · simp only [if_pos hp]
  · simp only [if_neg hp]
    obtain ⟨L, R, h⟩ := prod_ofFn_update_eq_mul F k
    rw [h, mul_zero, zero_mul]

theorem commutator_prod_ofFn_eq_sum_update {A : Type*} [Ring A] (X : A) : ∀ {t : ℕ} (F : Fin t → A),
    X * (List.ofFn F).prod - (List.ofFn F).prod * X =
      ∑ k, (List.ofFn (Function.update F k (X * F k - F k * X))).prod
  | 0, F => by simp
  | t + 1, F => by
    have ih := commutator_prod_ofFn_eq_sum_update X (fun i : Fin t => F i.succ)
    rw [Fin.sum_univ_succ]
    have h0 : (List.ofFn (Function.update F 0 (X * F 0 - F 0 * X))).prod =
        (X * F 0 - F 0 * X) * (List.ofFn fun i : Fin t => F i.succ).prod := by
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    have hs : ∀ k : Fin t, (List.ofFn (Function.update F k.succ (X * F k.succ - F k.succ * X))).prod =
        F 0 * (List.ofFn (Function.update (fun i : Fin t => F i.succ) k
          (X * F k.succ - F k.succ * X))).prod := by
      intro k
      have hf : (fun i : Fin t => Function.update F k.succ (X * F k.succ - F k.succ * X) i.succ) =
          Function.update (fun i : Fin t => F i.succ) k (X * F k.succ - F k.succ * X) := by
        funext i; simp [Function.update_apply, Fin.succ_inj]
      rw [List.ofFn_succ, List.prod_cons, hf]
      simp [Function.update_apply, (Fin.succ_ne_zero k).symm]
    rw [h0, Finset.sum_congr rfl (fun k _ => hs k), ← Finset.mul_sum, ← ih, List.ofFn_succ,
      List.prod_cons]
    noncomm_ring

theorem shiftedGenerator_commutator {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (v : ℂ) (a b c d : Fin n) :
    E c d * Tm E v a b - Tm E v a b * E c d =
      (if d = a then Tm E v c b else 0) - (if b = c then Tm E v a d else 0) := by
  have hc := hE c d a b
  have hcomm : E c d * (if a = b then algebraMap ℂ A v else 0) =
      (if a = b then algebraMap ℂ A v else 0) * E c d := by
    by_cases hab : a = b
    · simp only [if_pos hab]
      exact (Algebra.commutes v (E c d)).symm
    · simp only [if_neg hab, mul_zero, zero_mul]
  have key : E c d * Tm E v a b - Tm E v a b * E c d =
      E c d * E a b - E a b * E c d := by
    unfold Tm
    rw [mul_add, add_mul, hcomm]
    abel
  rw [key, hc]
  unfold Tm
  by_cases h1 : d = a
  · by_cases h2 : b = c
    · subst h1; subst h2; simp
    · subst h1; simp [h2, Ne.symm h2]
  · by_cases h2 : b = c
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2]

theorem eq_zero_of_eq_neg_self_of_algebra_complex {A : Type*} [Ring A] [Algebra ℂ A] (x : A) (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    calc x + x = -x + x := by rw [← h]
    _ = 0 := by simp
  have h3 : x = (2 : ℂ)⁻¹ • ((2 : ℂ) • x) := by
    rw [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]
  rw [h3, h2, smul_zero]

theorem comp_swap_of_eq {α β : Type*} [DecidableEq α] (f : α → β) (p q : α) (h : f p = f q) :
    f ∘ Equiv.swap p q = f := by
  funext x
  rw [Function.comp_apply, Equiv.swap_apply_def]
  by_cases h1 : x = p
  · rw [if_pos h1, h1]; exact h.symm
  · rw [if_neg h1]
    by_cases h2 : x = q
    · rw [if_pos h2, h2]; exact h
    · rw [if_neg h2]

theorem quantumMinor_eq_zero_of_row_eq (hr : QSkewRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) (p q : Fin t) (hpq : p ≠ q)
    (h : a p = a q) : qminor E a b u = 0 := by
  have h1 := hr A n t E a b (Equiv.swap p q) u
  rw [comp_swap_of_eq a p q h, Equiv.Perm.sign_swap hpq, Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one, neg_one_mul] at h1
  exact eq_zero_of_eq_neg_self_of_algebra_complex _ h1

theorem quantumMinor_eq_zero_of_col_eq (hc : QSkewCol) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (a b : Fin t → Fin n) (u : ℂ) (p q : Fin t)
    (hpq : p ≠ q) (h : b p = b q) : qminor E a b u = 0 := by
  have h1 := hc A n t E hE a b (Equiv.swap p q) u
  rw [comp_swap_of_eq b p q h, Equiv.Perm.sign_swap hpq, Units.val_neg, Units.val_one, Int.cast_neg,
    Int.cast_one, neg_one_mul] at h1
  exact eq_zero_of_eq_neg_self_of_algebra_complex _ h1

theorem generator_commutator_quantumDet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (u : ℂ) (c d : Fin n) :
    E c d * qdet E u - qdet E u * E c d =
      qminor E (Function.update id d c) id u - qminor E id (Function.update id c d) u := by
  have hs : ∀ (z : ℤ) (X P : A), X * ((z : A) * P) - (z : A) * P * X = (z : A) * (X * P - P * X) := by
    intro z X P
    simp only [mul_sub, ← mul_assoc, (Int.cast_commute z X).eq]
  unfold qdet qminor
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [hs, ← mul_sub]
  congr 1
  rw [commutator_prod_ofFn_eq_sum_update]
  simp only [shiftedGenerator_commutator E hE, prod_ofFn_update_sub, prod_ofFn_update_ite,
    Finset.sum_sub_distrib, id_eq]
  congr 1
  · rw [Finset.sum_eq_single (σ.symm d)]
    · rw [if_pos (σ.apply_symm_apply d).symm]
      congr 1
      congr 1
      funext k
      rw [Function.update_apply, Function.update_apply]
      by_cases hk : k = σ.symm d
      · rw [if_pos hk, if_pos (show σ k = d by rw [hk, Equiv.apply_symm_apply])]
        subst hk
        rfl
      · rw [if_neg hk, if_neg (show ¬ σ k = d from fun h => hk (by rw [← h, Equiv.symm_apply_apply]))]
        try rfl
    · intro b _ hb
      rw [if_neg (show ¬ d = σ b from fun h => hb (by rw [h, Equiv.symm_apply_apply]))]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    congr 1
    funext k
    rw [Function.update_apply, Function.update_apply]
    by_cases hk : k = c
    · rw [if_pos hk, if_pos hk]
      subst hk
      rfl
    · rw [if_neg hk, if_neg hk]
      try rfl

theorem qDetCentral_of (hr : QSkewRow) (hc : QSkewCol) : QDetCentral := by
  unfold QDetCentral
  intro A _ _ n E hE u c d
  have h := generator_commutator_quantumDet E hE u c d
  have key : qminor E (Function.update id d c) id u - qminor E id (Function.update id c d) u = 0 := by
    by_cases hcd : c = d
    · rw [hcd]
      have hid : Function.update (id : Fin n → Fin n) d d = id := by
        funext x
        by_cases hx : x = d
        · subst hx; simp
        · simp [hx]
      rw [hid, sub_self]
    · rw [quantumMinor_eq_zero_of_row_eq hr E (Function.update (id : Fin n → Fin n) d c) id u c d hcd
          (by simp [hcd]),
        quantumMinor_eq_zero_of_col_eq hc E hE id (Function.update (id : Fin n → Fin n) c d) u c d hcd
          (by simp [Ne.symm hcd]), sub_zero]
  rw [key, sub_eq_zero] at h
  exact h.symm

def cycleToLast (m : ℕ) (j : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  (Fin.revPerm.trans (Fin.cycleRange j.rev).symm).trans Fin.revPerm

theorem cycleToLast_castSucc (m : ℕ) (j : Fin (m + 1)) (k : Fin m) :
    cycleToLast m j k.castSucc = j.succAbove k := by
  simp only [cycleToLast, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_castSucc, Fin.cycleRange_symm_succ,
    Fin.rev_succAbove, Fin.rev_rev]

theorem cycleToLast_last (m : ℕ) (j : Fin (m + 1)) : cycleToLast m j (Fin.last m) = j := by
  simp only [cycleToLast, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_last, Fin.cycleRange_symm_zero, Fin.rev_rev]

theorem sign_cycleToLast (m : ℕ) (j : Fin (m + 1)) :
    Equiv.Perm.sign (cycleToLast m j) = (-1) ^ (m - (j : ℕ)) := by
  rw [cycleToLast, Equiv.Perm.sign_trans, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Fin.val_rev, mul_left_comm, Int.units_mul_self, mul_one]
  congr 1
  omega

def extendLast {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (finSuccEquivLast.trans (Equiv.optionCongr τ)).trans finSuccEquivLast.symm

theorem extendLast_castSucc {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) :
    extendLast τ k.castSucc = (τ k).castSucc := by
  simp [extendLast, finSuccEquivLast_castSucc, finSuccEquivLast_symm_some]

theorem extendLast_last {m : ℕ} (τ : Equiv.Perm (Fin m)) : extendLast τ (Fin.last m) = Fin.last m := by
  simp [extendLast, finSuccEquivLast_last, finSuccEquivLast_symm_none]

theorem sign_extendLast {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extendLast τ) = Equiv.Perm.sign τ := by
  rw [extendLast, Equiv.Perm.sign_trans_trans_symm]
  exact Equiv.optionCongr_sign τ

def lastColumnSplit (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  cycleToLast m p.1 * extendLast p.2

theorem lastColumnSplit_bijective (m : ℕ) : Function.Bijective (lastColumnSplit m) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    simp only [lastColumnSplit] at h
    have hj : j = j' := by
      have h' := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ (Fin.last m)) h
      simpa [Equiv.Perm.mul_apply, extendLast_last, cycleToLast_last] using h'
    subst hj
    have he : extendLast τ = extendLast τ' := mul_left_cancel h
    have hτ : τ = τ' := by
      refine Equiv.ext (fun k => ?_)
      have h' := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.castSucc) he
      simpa [extendLast_castSucc] using h'
    rw [hτ]
  · simp [Fintype.card_perm, Nat.factorial_succ]

theorem quantumMinor_expand_last {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminor E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) *
      qminor E (a ∘ Fin.succAbove j) (b ∘ Fin.castSucc) u * Tm E (u - (m : ℂ)) (a j) (b (Fin.last m)) := by
  unfold qminor
  rw [← (Equiv.ofBijective _ (lastColumnSplit_bijective m)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  simp only [Equiv.ofBijective_apply, lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast,
    Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_mul,
    List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    Equiv.Perm.mul_apply, extendLast_castSucc, cycleToLast_castSucc, extendLast_last, cycleToLast_last,
    Fin.val_castSucc, Fin.val_last, Function.comp_apply, mul_assoc]

theorem qComatrix_of (hr : QSkewRow) (hc : QSkewCol) : QComatrix := by
  unfold QComatrix
  intro A _ _ m E hE u i l
  obtain ⟨b', hbc, hbl⟩ : ∃ b' : Fin (m + 1) → Fin (m + 1),
      (∀ k : Fin m, b' k.castSucc = i.succAbove k) ∧ b' (Fin.last m) = l :=
    ⟨Fin.snoc (α := fun _ => Fin (m + 1)) (fun k => i.succAbove k) l, fun k => by simp, by simp⟩
  have hexp := quantumMinor_expand_last E id b' u
  have hbc' : b' ∘ Fin.castSucc = Fin.succAbove i := funext hbc
  rw [hbc', hbl] at hexp
  simp only [Function.id_comp, id_eq] at hexp
  have hsign : ∀ j : Fin (m + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) =
      (-1) ^ (m - (i : ℕ)) * (-1) ^ (m - (j : ℕ)) := by
    intro j
    rw [← pow_add]
    have hi := i.isLt
    have hj := j.isLt
    rcases Nat.even_or_odd ((i : ℕ) + j) with h | h
    · rw [h.neg_one_pow, Even.neg_one_pow]
      rw [Nat.even_iff] at h ⊢
      omega
    · rw [h.neg_one_pow, Odd.neg_one_pow]
      rw [Nat.odd_iff] at h ⊢
      omega
  have hL : ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
          qminor E (Fin.succAbove j) (Fin.succAbove i) u * Tm E (u - (m : ℂ)) j l =
      (((-1 : ℤ) ^ (m - (i : ℕ)) : ℤ) : A) * qminor E id b' u := by
    rw [hexp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hsign j, Int.cast_mul, mul_assoc]
  rw [hL]
  by_cases hil : i = l
  · rw [if_pos hil, qdet]
    have hb : b' = id ∘ (cycleToLast m i) := by
      funext x
      refine Fin.lastCases ?_ (fun k => ?_) x
      · rw [hbl]; simp [cycleToLast_last, hil]
      · rw [hbc]; simp [cycleToLast_castSucc]
    rw [hb, hc A (m + 1) (m + 1) E hE id id (cycleToLast m i) u, sign_cycleToLast,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_assoc, ← Int.cast_mul, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, Int.cast_one, one_mul]
  · rw [if_neg hil]
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Ne.symm hil)
    rw [quantumMinor_eq_zero_of_col_eq hc E hE id b' u z.castSucc (Fin.last m) (Fin.castSucc_lt_last z).ne
      (by rw [hbc, hbl, hz]), mul_zero]

end Formalism.REAL
