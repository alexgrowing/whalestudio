import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

section SlopeTestRemainingChoices

variable {𝒰 : Type*} [Ring 𝒰]

theorem prod_ofFn_update_eq {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) :
    ∃ A B : 𝒰, ∀ v, (List.ofFn (Function.update f j v)).prod = A * v * B := by
  induction p with
  | zero => exact j.elim0
  | succ p ih =>
    refine Fin.cases ?_ (fun j' => ?_) j
    · refine ⟨1, (List.ofFn fun i : Fin p => f i.succ).prod, fun v => ?_⟩
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    · obtain ⟨A, B, h⟩ := ih (fun i => f i.succ) j'
      refine ⟨f 0 * A, B, fun v => ?_⟩
      have e1 : (fun i : Fin p => Function.update f j'.succ v i.succ) =
          Function.update (fun i => f i.succ) j' v := by
        funext i
        simp only [Function.update_apply, Fin.succ_inj]
      have e2 : Function.update f j'.succ v 0 = f 0 := by
        simp only [Function.update_apply, (Fin.succ_ne_zero j').symm, if_false]
      rw [List.ofFn_succ, List.prod_cons, e1, e2, h]
      simp only [mul_assoc]

theorem comm_prod_ofFn (y : 𝒰) {p : ℕ} (f : Fin p → 𝒰) :
    y * (List.ofFn f).prod - (List.ofFn f).prod * y =
      ∑ j, (List.ofFn (Function.update f j (y * f j - f j * y))).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h0 : (List.ofFn (Function.update f 0 (y * f 0 - f 0 * y))).prod =
        (y * f 0 - f 0 * y) * (List.ofFn fun i : Fin p => f i.succ).prod := by
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    have hs : ∀ j' : Fin p,
        (List.ofFn (Function.update f j'.succ (y * f j'.succ - f j'.succ * y))).prod =
          f 0 * (List.ofFn (Function.update (fun i : Fin p => f i.succ) j'
            (y * f j'.succ - f j'.succ * y))).prod := by
      intro j'
      have e1 : (fun i : Fin p => Function.update f j'.succ (y * f j'.succ - f j'.succ * y) i.succ) =
          Function.update (fun i => f i.succ) j' (y * f j'.succ - f j'.succ * y) := by
        funext i
        simp only [Function.update_apply, Fin.succ_inj]
      have e2 : Function.update f j'.succ (y * f j'.succ - f j'.succ * y) 0 = f 0 := by
        simp only [Function.update_apply, (Fin.succ_ne_zero j').symm, if_false]
      rw [List.ofFn_succ, List.prod_cons, e1, e2]
    have hih := ih (fun i => f i.succ)
    rw [Fin.sum_univ_succ, h0, Finset.sum_congr rfl (fun j' _ => hs j'), ← Finset.mul_sum, ← hih,
      List.ofFn_succ, List.prod_cons]
    noncomm_ring

end SlopeTestRemainingChoices

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem capEntry_comm (hE : GlRelR E) (a b c d : Fin n) (x : ℂ) :
    E a b * capEntry E x c d - capEntry E x c d * E a b =
      (if b = c then capEntry E x a d else 0) - (if d = a then capEntry E x c b else 0) := by
  have hz : ∀ s : 𝒰, (s = 0 ∨ ∃ z : ℂ, s = algebraMap ℂ 𝒰 z) → E a b * s - s * E a b = 0 := by
    rintro s (rfl | ⟨z, rfl⟩)
    · simp
    · rw [Algebra.commutes, sub_self]
  have key : E a b * capEntry E x c d - capEntry E x c d * E a b =
      (E a b * E c d - E c d * E a b) + (E a b * (if c = d then algebraMap ℂ 𝒰 x else 0) -
        (if c = d then algebraMap ℂ 𝒰 x else 0) * E a b) := by
    unfold capEntry
    noncomm_ring
  have hs : (if c = d then algebraMap ℂ 𝒰 x else 0) = 0 ∨
      ∃ z : ℂ, (if c = d then algebraMap ℂ 𝒰 x else 0) = algebraMap ℂ 𝒰 z := by
    split_ifs
    · exact Or.inr ⟨x, rfl⟩
    · exact Or.inl rfl
  rw [key, hz _ hs, add_zero, hE a b c d]
  unfold capEntry
  split_ifs <;> subst_vars <;> first | rfl | simp_all | abel

private theorem prod_ofFn_update_sub' {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) (u v : 𝒰) :
    (List.ofFn (Function.update f j (u - v))).prod =
      (List.ofFn (Function.update f j u)).prod - (List.ofFn (Function.update f j v)).prod := by
  obtain ⟨A, B, h⟩ := prod_ofFn_update_eq f j
  rw [h, h, h]
  noncomm_ring

private theorem prod_ofFn_update_ite' {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) (P : Prop) [Decidable P]
    (w : 𝒰) :
    (List.ofFn (Function.update f j (if P then w else 0))).prod =
      if P then (List.ofFn (Function.update f j w)).prod else 0 := by
  obtain ⟨A, B, h⟩ := prod_ofFn_update_eq f j
  split_ifs
  · rfl
  · rw [h, mul_zero, zero_mul]

private theorem sum_ite_sum_comm {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop)
    [DecidablePred P] (g : α → β → 𝒰) :
    (∑ t, if P t then ∑ σ, g t σ else 0) = ∑ σ, ∑ t, if P t then g t σ else 0 := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

private theorem sum_comp_perm_eq_sum {p : ℕ} (σ : Equiv.Perm (Fin p)) (g : Fin p → 𝒰) :
    ∑ t, g t = ∑ j, g (σ j) :=
  (Equiv.sum_comp σ g).symm

theorem cminor_comm (hE : GlRelR E) (a b : Fin n) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    E a b * cminor E R C x - cminor E R C x * E a b =
      (∑ t : Fin p, if R t = b then cminor E (Function.update R t a) C x else 0) -
        ∑ t : Fin p, if C t = a then cminor E R (Function.update C t b) x else 0 := by
  unfold cminor
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_smul_comm, smul_mul_assoc,
    ← smul_sub, comm_prod_ofFn, capEntry_comm E hE, prod_ofFn_update_sub', prod_ofFn_update_ite']
  simp only [Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [sum_ite_sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    conv_rhs => rw [sum_comp_perm_eq_sum σ]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : R (σ j) = b
    · rw [if_pos h.symm, if_pos h]
      congr 1
      congr 1
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_apply, hk, σ.injective.ne hk]
    · rw [if_neg (Ne.symm h), if_neg h, smul_zero]
  · rw [sum_ite_sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : C j = a
    · rw [if_pos h, if_pos h]
      congr 1
      congr 1
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_apply, hk]
    · rw [if_neg h, if_neg h, smul_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
