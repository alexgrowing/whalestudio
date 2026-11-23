import Formalism.HermitianCurvature.StatementQ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.Qx6

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

def ext0 {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, τ)

theorem matrixExtendByZero_zero {m : ℕ} (τ : Equiv.Perm (Fin m)) : ext0 τ 0 = 0 := by
  simp [ext0, Equiv.Perm.decomposeFin_symm_apply_zero]

theorem extByZero_succ {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) : ext0 τ k.succ = (τ k).succ := by
  simp [ext0, Equiv.Perm.decomposeFin_symm_apply_succ]

theorem sign_extend_perm {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm.sign (ext0 τ) = Equiv.Perm.sign τ := by
  simp [ext0, Equiv.Perm.decomposeFin.symm_sign]

def phi0 (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (Fin.cycleRange p.1).symm * ext0 p.2

theorem firstColumnSplit_zero (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : phi0 m p 0 = p.1 := by
  simp [phi0, Equiv.Perm.mul_apply, matrixExtendByZero_zero, Fin.cycleRange_symm_zero]

theorem firstColumnSplit_succ (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) (k : Fin m) :
    phi0 m p k.succ = p.1.succAbove (p.2 k) := by
  simp [phi0, Equiv.Perm.mul_apply, extByZero_succ, Fin.cycleRange_symm_succ]

theorem sign_insert_perm (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (phi0 m p) = (-1) ^ (p.1 : ℕ) * Equiv.Perm.sign p.2 := by
  rw [phi0, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange, sign_extend_perm]

theorem firstColumnSplit_bijective (m : ℕ) : Function.Bijective (phi0 m) := by
  have hinj : Function.Injective (phi0 m) := by
    rintro ⟨i, σ⟩ ⟨j, τ⟩ h
    have h0 : i = j := by
      have h1 := congrArg (fun π : Equiv.Perm (Fin (m + 1)) => π 0) h
      simpa only [firstColumnSplit_zero] using h1
    subst h0
    have hs : σ = τ := by
      apply Equiv.ext
      intro k
      have h1 := congrArg (fun π : Equiv.Perm (Fin (m + 1)) => π k.succ) h
      simp only [firstColumnSplit_succ] at h1
      exact Fin.succAbove_right_injective h1
    rw [hs]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  simp [Fintype.card_perm, Fintype.card_prod, Nat.factorial_succ]

theorem rowExpFirst {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
        (Tm E (u - (t : ℂ)) (a 0) (b l) * qminorRow E (a ∘ Fin.succ) (b ∘ l.succAbove) u) := by
  unfold qminorRow
  rw [(Fintype.sum_bijective _ (firstColumnSplit_bijective t) _ _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [List.ofFn_succ, List.prod_cons]
  simp only [sign_insert_perm, firstColumnSplit_zero, firstColumnSplit_succ, Function.comp, Fin.val_zero, Fin.val_succ]
  have e1 : u - ((t + 1 : ℕ) : ℂ) + 1 + ((0 : ℕ) : ℂ) = u - (t : ℂ) := by push_cast; ring
  have e2 : ∀ i : Fin t, u - ((t + 1 : ℕ) : ℂ) + 1 + (((i : ℕ) + 1 : ℕ) : ℂ) = u - (t : ℂ) + 1 + ((i : ℕ) : ℂ) := by
    intro i; push_cast; ring
  simp only [e1, e2]
  have hc : ∀ x : A, ((Equiv.Perm.sign τ : ℤ) : A) * x = x * ((Equiv.Perm.sign τ : ℤ) : A) :=
    fun x => (Int.cast_commute _ _).eq
  push_cast
  simp only [mul_assoc]
  rw [← mul_assoc (Tm E (u - (t : ℂ)) (a 0) (b j)), ← hc, mul_assoc]

theorem rowExpLast {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
        (qminorRow E (a ∘ Fin.castSucc) (b ∘ l.succAbove) (u - 1) * Tm E u (a (Fin.last t)) (b l)) := by
  unfold qminorRow
  rw [(Fintype.sum_bijective _ (lastColumnSplit_bijective t) _ _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  simp only [lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast, Equiv.Perm.mul_apply,
    extendLast_castSucc, cycleToLast_castSucc, extendLast_last, cycleToLast_last, Fin.val_castSucc, Fin.val_last,
    Function.comp]
  have e1 : u - ((t + 1 : ℕ) : ℂ) + 1 + (t : ℂ) = u := by push_cast; ring
  have e2 : ∀ i : Fin t, u - ((t + 1 : ℕ) : ℂ) + 1 + ((i : ℕ) : ℂ) = u - 1 - (t : ℂ) + 1 + ((i : ℕ) : ℂ) := by
    intro i; push_cast; ring
  simp only [e1, e2]
  have hj : (j : ℕ) ≤ t := Nat.lt_succ_iff.mp j.isLt
  have hs : (-1 : ℤ) ^ (t + (j : ℕ)) = (-1) ^ (t - (j : ℕ)) := by
    rw [show t + (j : ℕ) = (t - (j : ℕ)) + 2 * (j : ℕ) by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [hs]
  push_cast
  simp only [mul_assoc]

theorem expRows : ExpRowsFromRowForm := by
  intro hRF
  refine ⟨?_, ?_⟩
  · intro A _ _ n t E hE a b u
    rw [hRF A n (t + 1) E hE a b u, rowExpFirst E a b u]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hRF A n t E hE (a ∘ Fin.succ) (b ∘ l.succAbove) u]
  · intro A _ _ n t E hE a b u
    rw [hRF A n (t + 1) E hE a b u, rowExpLast E a b u]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hRF A n t E hE (a ∘ Fin.castSucc) (b ∘ l.succAbove) (u - 1)]

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem skip_one_eq_succAbove {t : ℕ} (i : Fin (t + 1)) : (skip1 i : Fin t → Fin (t + 1)) = i.succAbove := by
  funext j
  apply Fin.ext
  simp only [skip1]
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc]; exact h)]
    try rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_iff_val_le_val, Fin.coe_castSucc]; omega)]
    try rfl

theorem skip_two_succAbove_comp_alt {t : ℕ} (b : Fin (t + 2)) (a : Fin (t + 1)) :
    (skip2 (min (b.succAbove a) b) (max (b.succAbove a) b) : Fin t → Fin (t + 2)) =
      b.succAbove ∘ a.succAbove := by
  funext j
  apply Fin.ext
  by_cases h : a.castSucc < b
  · have h1 : b.succAbove a = a.castSucc := Fin.succAbove_of_castSucc_lt _ _ h
    have h2 : min (b.succAbove a) b = a.castSucc := by rw [h1]; exact min_eq_left h.le
    have h3 : max (b.succAbove a) b = b := by rw [h1]; exact max_eq_right h.le
    rw [h2, h3]
    simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Function.comp] at h ⊢
    split_ifs <;> simp at * <;> omega
  · have h' : b ≤ a.castSucc := not_lt.mp h
    have h1 : b.succAbove a = a.succ := Fin.succAbove_of_le_castSucc _ _ h'
    have h4 : b ≤ a.succ := h'.trans (Fin.castSucc_lt_succ).le
    have h2 : min (b.succAbove a) b = b := by rw [h1]; exact min_eq_right h4
    have h3 : max (b.succAbove a) b = a.succ := by rw [h1]; exact max_eq_left h4
    rw [h2, h3]
    simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.val_castSucc, Function.comp, Fin.val_succ] at h' ⊢
    split_ifs <;> simp at * <;> omega

theorem sign_pair_succAbove_right {t : ℕ} (b : Fin (t + 1)) (a : Fin t) :
    sg2 b (b.succAbove a) = (-1) ^ ((b : ℕ) + (a : ℕ)) := by
  unfold sg2
  rcases lt_or_ge (Fin.castSucc a) b with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have h1 : (a : ℕ) < (b : ℕ) := h
    have h' : ((Fin.castSucc a : Fin (t + 1)) : ℕ) < (b : ℕ) := by rw [Fin.coe_castSucc]; exact h1
    rw [if_pos h', Fin.coe_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ h]
    have h1 : (b : ℕ) ≤ (a : ℕ) := h
    have h' : ¬ (((Fin.succ a : Fin (t + 1)) : ℕ) < (b : ℕ)) := by rw [Fin.val_succ]; omega
    rw [if_neg h', Fin.val_succ]
    ring

theorem sign_two_succAbove_left {t : ℕ} (b : Fin (t + 1)) (a : Fin t) :
    sg2 (b.succAbove a) b = (-1) ^ ((b : ℕ) + (a : ℕ) + 1) := by
  unfold sg2
  rcases lt_or_ge (Fin.castSucc a) b with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have h1 : (a : ℕ) < (b : ℕ) := h
    have h' : ¬ ((b : ℕ) < ((Fin.castSucc a : Fin (t + 1)) : ℕ)) := by rw [Fin.coe_castSucc]; omega
    rw [if_neg h', Fin.coe_castSucc]
    ring
  · rw [Fin.succAbove_of_le_castSucc _ _ h]
    have h1 : (b : ℕ) ≤ (a : ℕ) := h
    have h' : (b : ℕ) < ((Fin.succ a : Fin (t + 1)) : ℕ) := by rw [Fin.val_succ]; omega
    rw [if_pos h', Fin.val_succ]
    ring

section lists
variable {n : ℕ}

@[simp] theorem bE_zero {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bE e v 0 = e := rfl
@[simp] theorem bE_succ {m : ℕ} (e : Fin n) (v : Fin m → Fin n) (j : Fin m) : bE e v j.succ = v j := rfl
@[simp] theorem bS_last {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bS v e (Fin.last m) = e := by
  simp [bS]
@[simp] theorem bS_castSucc {m : ℕ} (e : Fin n) (v : Fin m → Fin n) (j : Fin m) : bS v e j.castSucc = v j := by
  simp [bS]

theorem bE_comp_succ {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bE e v ∘ Fin.succ = v := rfl
theorem bS_comp_castSucc {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bS v e ∘ Fin.castSucc = v := by
  funext j
  simp [bS]

theorem bE_bS {m : ℕ} (e es : Fin n) (v : Fin m → Fin n) : bE e (bS v es) = bS (bE e v) es := by
  simp only [bE, bS]
  exact Fin.cons_snoc_eq_snoc_cons _ _ _

theorem bE_succAbove_zero {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bE e v ∘ (0 : Fin (m + 1)).succAbove = v := by
  funext j
  simp [bE, Fin.succAbove_zero]

theorem bS_succAbove_last {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bS v e ∘ (Fin.last m).succAbove = v := by
  funext j
  simp [bS, Fin.succAbove_last]

theorem bE_succAbove_succ {m : ℕ} (e : Fin n) (v : Fin (m + 1) → Fin n) (w : Fin (m + 1)) :
    bE e v ∘ w.succ.succAbove = bE e (v ∘ w.succAbove) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [bE, Fin.succ_succAbove_zero]
  | succ k => simp [bE, Fin.succ_succAbove_succ]

theorem bS_succAbove_castSucc {m : ℕ} (e : Fin n) (v : Fin (m + 1) → Fin n) (w : Fin (m + 1)) :
    bS v e ∘ w.castSucc.succAbove = bS (v ∘ w.succAbove) e := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [Function.comp_apply, Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _)), Fin.succ_last]
    simp [bS]
  | cast k => simp [bS, Fin.castSucc_succAbove_castSucc]

theorem bE_cyc {m : ℕ} (e : Fin n) (v : Fin m → Fin n) : bE e v ∘ cycleToLast m 0 = bS v e := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    have h : cycleToLast m 0 (Fin.last m) = 0 := by
      simp only [cycleToLast, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_last, Fin.rev_zero, Fin.cycleRange_symm_zero]
    rw [Function.comp_apply, h, bS_last, bE_zero]
  | cast k =>
    have h : cycleToLast m 0 (Fin.castSucc k) = k.succ := by
      simp only [cycleToLast, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_zero, Fin.cycleRange_symm_succ,
        Fin.succAbove_last, Fin.rev_rev]
    rw [Function.comp_apply, h, bS_castSucc, bE_succ]

end lists

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem sgn_congr {a b : ℕ} (h : a % 2 = b % 2) : (-1 : ℤ) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

theorem Tm_ne {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) {a b : Fin n}
    (h : a ≠ b) : Tm E u a b = E a b := by
  simp [Tm, h]

theorem add_eq_sub_of {G : Type*} [AddGroup G] {x y z : G} (h : y = -z) : x + y = x - z := by
  rw [h, sub_eq_add_neg]

section exp
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem qm_bS_eq (hSk : QSkewRow) {t : ℕ} (f : Fin t → Fin n) (e : Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bS f e) b u = ((-1 : ℤ) ^ t) • qminor E (bE e f) b u := by
  have hs : Equiv.Perm.sign (cycleToLast t 0) = (-1) ^ t := by
    simp only [cycleToLast, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, Fin.rev_zero, Fin.sign_cycleRange, Fin.val_last]
    rw [mul_left_comm, Int.units_mul_self, mul_one]
  rw [← bE_cyc, hSk A n (t + 1) E (bE e f) b (cycleToLast t 0) u, hs, zsmul_eq_mul]
  push_cast
  rfl

theorem qm_bE_eq (hSk : QSkewRow) {t : ℕ} (f : Fin t → Fin n) (e : Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bE e f) b u = ((-1 : ℤ) ^ t) • qminor E (bS f e) b u := by
  rw [qm_bS_eq E hSk f e b u, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

theorem quantum_minor_expand_last_line (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E) {t : ℕ} (f : Fin t → Fin n) (e : Fin n)
    (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bE e f) b u = ∑ x : Fin (t + 1), ((-1 : ℤ) ^ (x : ℕ)) •
      (qminor E f (b ∘ x.succAbove) (u - 1) * Tm E u e (b x)) := by
  rw [qm_bE_eq E hSk f e b u, hLR A n t E hE (bS f e) b u, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hz : ((-1 : ℤ) ^ t) * (-1) ^ (t + (x : ℕ)) = (-1) ^ (x : ℕ) := by
    rw [← pow_add, show t + (t + (x : ℕ)) = (x : ℕ) + 2 * t by ring, pow_add, pow_mul]
    simp
  rw [bS_comp_castSucc, bS_last, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul, hz]

theorem quantum_minor_expand_first_line (hFR : ExpFirstRow) (hSk : QSkewRow) (hE : GlRel E) {t : ℕ} (f : Fin t → Fin n) (e : Fin n)
    (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bS f e) b u = ∑ x : Fin (t + 1), ((-1 : ℤ) ^ (t + (x : ℕ))) •
      (Tm E (u - (t : ℂ)) e (b x) * qminor E f (b ∘ x.succAbove) u) := by
  rw [qm_bS_eq E hSk f e b u, hFR A n t E hE (bE e f) b u, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [bE_zero, bE_comp_succ, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul, ← pow_add]

theorem expFCE (hFC : ExpFirstCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bE s f) (bE c b') u = Tm E u s c * qminor E f b' (u - 1) +
      ∑ w : Fin t, ((-1 : ℤ) ^ ((w : ℕ) + 1)) •
        (Tm E u (f w) c * qminor E (bE s f ∘ w.succ.succAbove) b' (u - 1)) := by
  rw [hFC A n t E (bE s f) (bE c b') u, Fin.sum_univ_succ]
  simp only [bE_zero, bE_succ, bE_comp_succ, bE_succAbove_zero, Fin.val_zero, Fin.val_succ, pow_zero,
    Int.cast_one, one_mul, zsmul_eq_mul]

theorem expFCS (hFC : ExpFirstCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bS f s) (bE c b') u =
      ∑ w : Fin t, ((-1 : ℤ) ^ (w : ℕ)) •
        (Tm E u (f w) c * qminor E (bS f s ∘ w.castSucc.succAbove) b' (u - 1)) +
      ((-1 : ℤ) ^ t) • (Tm E u s c * qminor E f b' (u - 1)) := by
  rw [hFC A n t E (bS f s) (bE c b') u, Fin.sum_univ_castSucc]
  simp only [bE_zero, bE_comp_succ, bS_castSucc, bS_last, bS_succAbove_last, Fin.coe_castSucc, Fin.val_last,
    zsmul_eq_mul]

theorem expLCS (hLC : ExpLastCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bS f s) (bS b' c) u =
      ∑ w : Fin t, ((-1 : ℤ) ^ (t + (w : ℕ))) •
        (qminor E (bS f s ∘ w.castSucc.succAbove) b' u * Tm E (u - (t : ℂ)) (f w) c) +
      qminor E f b' u * Tm E (u - (t : ℂ)) s c := by
  have h2 : ((-1 : ℤ) ^ (t + t)) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  rw [hLC A n t E (bS f s) (bS b' c) u, Fin.sum_univ_castSucc]
  simp only [bS_comp_castSucc, bS_last, bS_castSucc, bS_succAbove_last, Fin.coe_castSucc, Fin.val_last, h2,
    Int.cast_one, one_mul, zsmul_eq_mul]

theorem expLCE (hLC : ExpLastCol) {t : ℕ} (f b' : Fin t → Fin n) (s c : Fin n) (u : ℂ) :
    qminor E (bE s f) (bS b' c) u =
      ((-1 : ℤ) ^ t) • (qminor E f b' u * Tm E (u - (t : ℂ)) s c) +
      ∑ w : Fin t, ((-1 : ℤ) ^ (t + ((w : ℕ) + 1))) •
        (qminor E (bE s f ∘ w.succ.succAbove) b' u * Tm E (u - (t : ℂ)) (f w) c) := by
  rw [hLC A n t E (bE s f) (bS b' c) u, Fin.sum_univ_succ]
  simp only [bS_comp_castSucc, bS_last, bE_zero, bE_succ, bE_succAbove_zero, Fin.val_zero, Fin.val_succ, add_zero,
    zsmul_eq_mul]

theorem qm_dropS (hFR : ExpFirstRow) (hSk : QSkewRow) (hE : GlRel E) : ∀ {m : ℕ} (v b : Fin m → Fin n) (s : Fin n)
    (w : Fin m) (u : ℂ),
    qminor E (bS v s ∘ w.castSucc.succAbove) b u = ∑ x : Fin m, ((-1 : ℤ) ^ (m + 1 + (x : ℕ))) •
      (Tm E (u - (m : ℂ) + 1) s (b x) * qminor E (v ∘ skip1 w) (b ∘ skip1 x) u)
  | 0, _, _, _, w, _ => w.elim0
  | m + 1, v, b, s, w, u => by
    rw [bS_succAbove_castSucc, quantum_minor_expand_first_line E hFR hSk hE]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [sgn_congr (b := m + 1 + 1 + (x : ℕ)) (by omega)]
    have e1 : u - ((m + 1 : ℕ) : ℂ) + 1 = u - (m : ℂ) := by push_cast; ring
    rw [e1]
    rfl

theorem qm_dropE (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E) : ∀ {m : ℕ} (v b : Fin m → Fin n) (s : Fin n)
    (w : Fin m) (u : ℂ),
    qminor E (bE s v ∘ w.succ.succAbove) b u = ∑ x : Fin m, ((-1 : ℤ) ^ (x : ℕ)) •
      (qminor E (v ∘ skip1 w) (b ∘ skip1 x) (u - 1) * Tm E u s (b x))
  | 0, _, _, _, w, _ => w.elim0
  | m + 1, v, b, s, w, u => by
    rw [bE_succAbove_succ, quantum_minor_expand_last_line E hLR hSk hE]
    rfl

end exp

theorem borderE_of (hFC : ExpFirstCol) (hLR : ExpLastRow) (hSk : QSkewRow) : BorderE := by
  intro A _ _ n m E e es v hE hB u
  obtain ⟨_, _, hve, _⟩ := hB
  rw [expFCE E hFC]
  refine add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [qm_dropE E hLR hSk hE, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Tm_ne E _ (hve w), Tm_ne E _ (hve x).symm, ← zsmul_eq_mul, mul_smul_comm, smul_smul, ← pow_add, ← neg_smul,
    show u - 1 - 1 = u - 2 by ring, mul_assoc]
  congr 1
  rw [show (w : ℕ) + 1 + (x : ℕ) = (w : ℕ) + (x : ℕ) + 1 by ring, pow_succ]
  ring

theorem borderS_of (hLC : ExpLastCol) (hFR : ExpFirstRow) (hSk : QSkewRow) : BorderS := by
  intro A _ _ n m E e es v hE hB u
  obtain ⟨_, _, _, hvs⟩ := hB
  rw [expLCS E hLC, add_comm]
  refine add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [qm_dropS E hFR hSk hE, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Tm_ne E _ (hvs w), Tm_ne E _ (hvs x).symm, ← zsmul_eq_mul, smul_mul_assoc, smul_smul, ← pow_add, ← neg_smul]
  congr 1
  rw [sgn_congr (b := (w : ℕ) + (x : ℕ) + 1) (by omega), pow_succ]
  ring

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem Tm_comm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ)
    {a c d : Fin n} (h1 : a ≠ c) (h2 : d ≠ a) : Tm E u a a * E c d = E c d * Tm E u a a := by
  have h := hE a a c d
  rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
  simp only [Tm, eq_self_iff_true, if_true]
  rw [add_mul, mul_add, h, Algebra.commutes]

theorem sum_ne_succAbove {M : Type*} [AddCommMonoid M] {t : ℕ} (p : Fin (t + 1)) (f : Fin (t + 1) → M) :
    (∑ W, if W ≠ p then f W else 0) = ∑ w, f (p.succAbove w) := by
  rw [Fin.sum_univ_succAbove _ p]
  simp [Fin.succAbove_ne]

theorem sum3conv {M : Type*} [AddCommMonoid M] {t : ℕ} (w : Fin (t + 1)) (F : Fin (t + 1) → Fin (t + 1) → Fin (t + 1) → M) :
    (∑ W, ∑ X, ∑ X', if W ≠ w ∧ X ≠ X' then F W X X' else 0) =
      ∑ w', ∑ x', ∑ x, F (w.succAbove w') (x'.succAbove x) x' := by
  rw [Fin.sum_univ_succAbove _ w]
  have h0 : (∑ X, ∑ X', if w ≠ w ∧ X ≠ X' then F w X X' else (0 : M)) = 0 := by
    simp
  rw [h0, zero_add]
  refine Finset.sum_congr rfl (fun w' _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [Fin.sum_univ_succAbove _ x']
  simp [Fin.succAbove_ne]

theorem skip_two_comp_skip_one {n : ℕ} : ∀ {t : ℕ} (v : Fin (t + 1) → Fin n) (w : Fin (t + 1)) (w' : Fin t),
    (v ∘ skip2 (min (w.succAbove w') w) (max (w.succAbove w') w) : Fin (t + 1 - 2) → Fin n) =
      (v ∘ w.succAbove) ∘ skip1 w'
  | 0, _, _, w' => w'.elim0
  | t + 1, v, w, w' => by
    have h1 := skip_two_succAbove_comp_alt w w'
    have h2 := skip_one_eq_succAbove w'
    funext j
    have h3 := congrFun h1 j
    have h4 := congrFun h2 j
    simp only [Function.comp] at h3 ⊢
    rw [h3, h4]

section full
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem qm_drop2 (hFR : ExpFirstRow) (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E) {t : ℕ} (g : Fin t → Fin n)
    (b : Fin (t + 1) → Fin n) (e s : Fin n) (w : Fin t) (u : ℂ) :
    qminor E (bE e (bS g s) ∘ w.castSucc.succ.succAbove) b u =
      ∑ x' : Fin (t + 1), ∑ x : Fin t, ((-1 : ℤ) ^ ((x' : ℕ) + (t + 1 + (x : ℕ)))) •
        (Tm E (u - 1 - (t : ℂ) + 1) s (b (x'.succAbove x)) *
          qminor E (g ∘ skip1 w) ((b ∘ x'.succAbove) ∘ skip1 x) (u - 1) * Tm E u e (b x')) := by
  rw [bE_succAbove_succ, quantum_minor_expand_last_line E hLR hSk hE]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [qm_dropS E hFR hSk hE, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, smul_smul, ← pow_add]
  rfl

theorem qm_rowW (hFC : ExpFirstCol) (hFR : ExpFirstRow) (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E)
    (e es : Fin n) : ∀ {m : ℕ} (v : Fin m → Fin n), IsBorder e es v → ∀ (w : Fin m) (u : ℂ),
    qminor E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bE e v) u =
      Tm E u e e * qminor E (bS v es ∘ w.castSucc.succAbove) v (u - 1) +
      ((-1 : ℤ) ^ m) • (E es e * qminor E (bE e v ∘ w.succ.succAbove) v (u - 1)) +
      ∑ W : Fin m, ∑ X : Fin m, ∑ X' : Fin m, if W ≠ w ∧ X ≠ X' then
        ((-1 : ℤ) ^ (m + 1 + (w : ℕ)) * (sg2 W w * sg2 X X')) •
          (E (v W) e * E es (v X) *
            qminor E (v ∘ skip2 (min W w) (max W w)) (v ∘ skip2 (min X X') (max X X')) (u - 2) * E e (v X'))
        else 0
  | 0, _, _, w, _ => w.elim0
  | m + 1, v, hB, w, u => by
    obtain ⟨_, hee, hve, hvs⟩ := hB
    rw [sum3conv, bE_succAbove_succ, bS_succAbove_castSucc, expFCE E hFC, Fin.sum_univ_castSucc,
      add_assoc (Tm E u e e * _)]
    congr 1
    rw [add_comm (Finset.sum _ _)]
    congr 1
    · rw [bS_last, Tm_ne E _ hee.symm, bE_succAbove_succ, bS_succAbove_last, bE_succAbove_succ, Fin.val_last]
    · refine Finset.sum_congr rfl (fun w' _ => ?_)
      rw [qm_drop2 E hFR hLR hSk hE, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun x' _ => ?_)
      rw [Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [bS_castSucc, Function.comp, Tm_ne E _ (hve _), Tm_ne E _ (hvs _).symm, Tm_ne E _ (hve _).symm,
        mul_smul_comm, smul_smul, sign_two_succAbove_left, sign_two_succAbove_left, skip_two_comp_skip_one, skip_two_comp_skip_one, show u - 1 - 1 = u - 2 by ring,
        Fin.val_castSucc, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      · exact sgn_congr (by omega)
      · simp only [mul_assoc]

end full

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem snocCast_eq {n : ℕ} : ∀ {m : ℕ} (v : Fin m → Fin n) (es : Fin n) (w : Fin m) (h : m = m - 1 + 1),
    (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast h : Fin m → Fin n) =
      bS v es ∘ w.castSucc.succAbove
  | 0, _, _, w, _ => w.elim0
  | m + 1, v, es, w, h => by
    rw [bS_succAbove_castSucc]
    rfl

theorem borderFull_of (hFC : ExpFirstCol) (hLC : ExpLastCol) (hFR : ExpFirstRow) (hLR : ExpLastRow)
    (hSk : QSkewRow) : BorderFull := by
  intro A _ _ n m E e es v hE hB u
  have hBE := borderE_of hFC hLR hSk A n m E e es v hE hB u
  obtain ⟨hinj, hee, hve, hvs⟩ := id hB
  have r0 : bS (bE e v) es ∘ (Fin.castSucc 0).succAbove = bS v es := by
    rw [← bE_bS, Fin.castSucc_zero, bE_succAbove_zero]
  have rW : ∀ w : Fin m, bS (bE e v) es ∘ w.succ.castSucc.succAbove =
      bE e (bS v es) ∘ w.castSucc.succ.succAbove := by
    intro w; rw [← bE_bS, Fin.succ_castSucc]
  have e1 : u - ((m + 1 : ℕ) : ℂ) = u - (m : ℂ) - 1 := by push_cast; ring
  simp only [snocCast_eq]
  rw [bE_bS, expLCS E hLC, Fin.sum_univ_succ, r0, e1]
  simp only [rW, bE_zero, bE_succ, Fin.val_zero, Fin.val_succ]
  rw [Tm_ne E _ hee]
  simp only [Tm_ne E _ (hvs _)]
  set C := qminor E v v (u - 1) with hC
  set Tee := Tm E u e e with hTee
  set Tss := Tm E (u - (m : ℂ) - 1) es es with hTss
  set Z : A := ∑ w : Fin m, ((-1 : ℤ) ^ (w : ℕ)) •
    (E es e * qminor E (bE e v ∘ w.succ.succAbove) v (u - 1) * E (v w) es) with hZ
  have L1 : ((-1 : ℤ) ^ (m + 1 + 0)) • (qminor E (bS v es) (bE e v) u * E e es) =
      (∑ w : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (bS v es ∘ w.castSucc.succAbove) v (u - 1) * E e es)) -
        E es e * C * E e es := by
    rw [expFCS E hFC, add_mul, smul_add, Finset.sum_mul, Finset.smul_sum, Tm_ne E _ hee.symm, smul_mul_assoc,
      smul_smul, ← pow_add, sgn_congr (a := m + 1 + 0 + m) (b := 1) (by omega), pow_one, neg_one_smul, ← sub_eq_add_neg]
    congr 1
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Tm_ne E _ (hve w), smul_mul_assoc, smul_smul, ← pow_add, ← zsmul_eq_mul,
      sgn_congr (b := (w : ℕ) + 1 + m) (by omega)]
  have L3 : qminor E (bE e v) (bE e v) u * Tss = Tee * C * Tss -
      (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * Tss * E e (v x))) := by
    rw [hBE, sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_assoc, mul_assoc _ (E e (v x)) Tss, ← Tm_comm E hE _ hee.symm (hvs x), ← mul_assoc _ Tss]
  have R5 : (((-1 : ℤ) ^ (m + 1) : ℤ) : A) * (E es e * qminor E (bE e v) (bS v es) (u - 1)) =
      -(E es e * C * E e es) + Z := by
    rw [expLCE E hLC, Tm_ne E _ hee, mul_add, mul_add, ← zsmul_eq_mul, mul_smul_comm, smul_smul, ← pow_add,
      sgn_congr (a := m + 1 + m) (b := 1) (by omega), pow_one, neg_one_smul, mul_assoc]
    congr 1
    rw [Finset.mul_sum, ← zsmul_eq_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Tm_ne E _ (hvs w), mul_smul_comm, smul_smul, ← pow_add, sgn_congr (b := (w : ℕ)) (by omega), mul_assoc]
  have L2 : (∑ w : Fin m, ((-1 : ℤ) ^ (m + 1 + ((w : ℕ) + 1))) •
        (qminor E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bE e v) u * E (v w) es)) =
      -(∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E es (v x) * Tee * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 1) * E (v w) es)) + Z +
      -(∑ w : Fin m, ∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0) := by
    rw [Finset.sum_comm (f := fun w w' => ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0), hZ, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [qm_rowW E hFC hFR hLR hSk hE e es v hB, add_mul, add_mul, smul_add, smul_add]
    congr 1
    · congr 1
      · rw [qm_dropS E hFR hSk hE, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Tm_ne E _ (hvs x).symm, mul_smul_comm, smul_mul_assoc, smul_smul, ← pow_add, ← zsmul_eq_mul, ← neg_smul,
          ← mul_assoc, Tm_comm E hE _ hee (hve x)]
        congr 1
        rw [sgn_congr (b := (w : ℕ) + (x : ℕ) + 1) (by omega), pow_succ]
        ring
      · rw [smul_mul_assoc, smul_smul, ← pow_add, sgn_congr (b := (w : ℕ)) (by omega)]
    · rw [Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun W _ => ?_)
      rw [Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun X _ => ?_)
      rw [Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun X' _ => ?_)
      split_ifs with h
      · rw [smul_mul_assoc, smul_smul, ← zsmul_eq_mul, ← neg_smul, ← mul_assoc, ← pow_add]
        congr 1
        rw [sgn_congr (b := 1) (by omega)]
        ring
      · simp
  rw [L1, L2, L3, R5]
  abel

theorem borderFromExpansions : BorderFromExpansions := by
  intro hFC hLC hFR hLR hSk
  exact ⟨borderE_of hFC hLR hSk, borderS_of hLC hFR hSk, borderFull_of hFC hLC hFR hLR hSk⟩

end

section

structure HatData (X : Type*) [AddCommGroup X] [Module ℂ X] where
  G : Submodule ℂ X
  N : X →ₗ[ℂ] X
  N_mem : ∀ x ∈ G, N x ∈ G
  N_idem : ∀ x, N (N x) = N x

namespace HatData

variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)

def V : Submodule ℂ X where
  carrier := {x | x ∈ H.G ∧ H.N x = x}
  zero_mem' := ⟨H.G.zero_mem, map_zero _⟩
  add_mem' := fun ha hb => ⟨H.G.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2]⟩
  smul_mem' := fun s _ ha => ⟨H.G.smul_mem s ha.1, by rw [map_smul, ha.2]⟩

structure Good (T : X → X) : Prop where
  mem : ∀ x ∈ H.G, T x ∈ H.G
  congr : ∀ x ∈ H.G, ∀ y ∈ H.G, H.N x = H.N y → H.N (T x) = H.N (T y)
  lin : ∀ x ∈ H.G, ∀ y ∈ H.G, ∀ s : ℂ, H.N (T (x + s • y)) = H.N (T x) + s • H.N (T y)

def toV (x : X) (hx : x ∈ H.G) : H.V := ⟨H.N x, H.N_mem x hx, H.N_idem x⟩

variable {H}

theorem Good.map_zero {T : X → X} (h : H.Good T) : H.N (T 0) = 0 := by
  have h1 := h.lin 0 H.G.zero_mem 0 H.G.zero_mem 1
  rw [smul_zero, add_zero, one_smul] at h1
  have h2 := congrArg (fun v => v - H.N (T 0)) h1
  simp only [sub_self, add_sub_cancel_right] at h2
  exact h2.symm

theorem Good.map_smul {T : X → X} (h : H.Good T) {x : X} (hx : x ∈ H.G) (s : ℂ) :
    H.N (T (s • x)) = s • H.N (T x) := by
  have h1 := h.lin 0 H.G.zero_mem x hx s
  rw [zero_add, h.map_zero, zero_add] at h1
  exact h1

theorem Good.map_add {T : X → X} (h : H.Good T) {x y : X} (hx : x ∈ H.G) (hy : y ∈ H.G) :
    H.N (T (x + y)) = H.N (T x) + H.N (T y) := by
  simpa only [one_smul] using h.lin x hx y hy 1

variable (H)

open Classical in

def hat (T : X → X) : Module.End ℂ H.V :=
  if h : H.Good T then
    { toFun := fun x => H.toV (T x) (h.mem _ x.2.1)
      map_add' := fun x y => Subtype.ext (h.map_add x.2.1 y.2.1)
      map_smul' := fun s x => Subtype.ext (h.map_smul x.2.1 s) }
  else 0

variable {H}

theorem hat_apply {T : X → X} (h : H.Good T) (x : H.V) : ((H.hat T x : H.V) : X) = H.N (T x) := by
  unfold HatData.hat
  rw [dif_pos h] <;> rfl

theorem hat_toV {T : X → X} (h : H.Good T) {x : X} (hx : x ∈ H.G) :
    H.hat T (H.toV x hx) = H.toV (T x) (h.mem x hx) := by
  apply Subtype.ext
  rw [hat_apply h]
  exact h.congr _ (H.N_mem x hx) _ hx (H.N_idem x)

theorem Good.comp {T S : X → X} (hT : H.Good T) (hS : H.Good S) : H.Good (fun x => T (S x)) where
  mem := fun x hx => hT.mem _ (hS.mem x hx)
  congr := fun x hx y hy h => hT.congr _ (hS.mem x hx) _ (hS.mem y hy) (hS.congr x hx y hy h)
  lin := fun x hx y hy s => by
    have h1 : H.N (S (x + s • y)) = H.N (S x + s • S y) := by
      rw [hS.lin x hx y hy s, _root_.map_add, _root_.map_smul]
    rw [hT.congr _ (hS.mem _ (H.G.add_mem hx (H.G.smul_mem s hy))) _
      (H.G.add_mem (hS.mem x hx) (H.G.smul_mem s (hS.mem y hy))) h1]
    exact hT.lin _ (hS.mem x hx) _ (hS.mem y hy) s

theorem Good.add {T S : X → X} (hT : H.Good T) (hS : H.Good S) : H.Good (fun x => T x + S x) where
  mem := fun x hx => H.G.add_mem (hT.mem x hx) (hS.mem x hx)
  congr := fun x hx y hy h => by
    rw [_root_.map_add, _root_.map_add, hT.congr x hx y hy h, hS.congr x hx y hy h]
  lin := fun x hx y hy s => by
    rw [_root_.map_add, _root_.map_add, _root_.map_add, hT.lin x hx y hy s, hS.lin x hx y hy s, smul_add]
    abel

theorem Good.smul {T : X → X} (hT : H.Good T) (a : ℂ) : H.Good (fun x => a • T x) where
  mem := fun x hx => H.G.smul_mem a (hT.mem x hx)
  congr := fun x hx y hy h => by
    rw [_root_.map_smul, _root_.map_smul, hT.congr x hx y hy h]
  lin := fun x hx y hy s => by
    rw [_root_.map_smul, _root_.map_smul, _root_.map_smul, hT.lin x hx y hy s, smul_add, smul_comm]

theorem Good.neg {T : X → X} (hT : H.Good T) : H.Good (fun x => -T x) := by
  have e : (fun x => -T x) = fun x => (-1 : ℂ) • T x := by
    funext x
    simp
  rw [e]
  exact hT.smul (-1)

theorem Good.sub {T S : X → X} (hT : H.Good T) (hS : H.Good S) : H.Good (fun x => T x - S x) := by
  have e : (fun x => T x - S x) = fun x => T x + -S x := by
    funext x
    exact sub_eq_add_neg _ _
  rw [e]
  exact hT.add hS.neg

theorem good_id : H.Good (fun x => x) where
  mem := fun _ hx => hx
  congr := fun _ _ _ _ h => h
  lin := fun x _ y _ s => by rw [_root_.map_add, _root_.map_smul]

theorem good_zero : H.Good (fun _ => (0 : X)) where
  mem := fun _ _ => H.G.zero_mem
  congr := fun _ _ _ _ _ => rfl
  lin := fun _ _ _ _ _ => by simp

theorem hat_comp {T S : X → X} (hT : H.Good T) (hS : H.Good S) :
    H.hat (fun x => T (S x)) = H.hat T * H.hat S := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => T (S x)) x : H.V) : X) = ((H.hat T (H.hat S x) : H.V) : X)
  rw [hat_apply (hT.comp hS), hat_apply hT, hat_apply hS]
  exact hT.congr _ (hS.mem _ x.2.1) _ (H.N_mem _ (hS.mem _ x.2.1)) (H.N_idem _).symm

theorem hat_add {T S : X → X} (hT : H.Good T) (hS : H.Good S) :
    H.hat (fun x => T x + S x) = H.hat T + H.hat S := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => T x + S x) x : H.V) : X) = ((H.hat T x : H.V) : X) + ((H.hat S x : H.V) : X)
  rw [hat_apply (hT.add hS), hat_apply hT, hat_apply hS]
  exact map_add H.N _ _

theorem hat_smul {T : X → X} (hT : H.Good T) (a : ℂ) : H.hat (fun x => a • T x) = a • H.hat T := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => a • T x) x : H.V) : X) = a • ((H.hat T x : H.V) : X)
  rw [hat_apply (hT.smul a), hat_apply hT]
  exact map_smul H.N a _

theorem hat_neg {T : X → X} (hT : H.Good T) : H.hat (fun x => -T x) = -H.hat T := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => -T x) x : H.V) : X) = -((H.hat T x : H.V) : X)
  rw [hat_apply hT.neg, hat_apply hT]
  exact map_neg H.N _

theorem hat_sub {T S : X → X} (hT : H.Good T) (hS : H.Good S) :
    H.hat (fun x => T x - S x) = H.hat T - H.hat S := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => T x - S x) x : H.V) : X) = ((H.hat T x : H.V) : X) - ((H.hat S x : H.V) : X)
  rw [hat_apply (hT.sub hS), hat_apply hT, hat_apply hS]
  exact map_sub H.N _ _

theorem hat_id : H.hat (fun x => x) = 1 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun x => x) x : H.V) : X) = (x : X)
  rw [hat_apply good_id]
  exact x.2.2

theorem hat_zero : H.hat (fun _ => (0 : X)) = 0 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show ((H.hat (fun _ => (0 : X)) x : H.V) : X) = 0
  rw [hat_apply good_zero]
  exact map_zero H.N

end HatData

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

abbrev XX (k r : ℕ) := (Fin r → ℂ) × Mx k r

theorem filter_succ : ∀ {r : ℕ} (l : Fin r),
    (List.finRange r).filter (fun a => decide (a.val < l.val + 1)) =
      (List.finRange r).filter (fun a => decide (a.val < l.val)) ++ [l]
  | 0, l => l.elim0
  | r + 1, l => by
    rw [List.finRange_succ]
    simp only [List.filter_cons, List.filter_map]
    refine Fin.cases ?_ (fun l' => ?_) l
    · simp [Function.comp_def]
    · have ih := filter_succ l'
      simp only [Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, decide_true, if_true, Function.comp_def,
        Nat.add_lt_add_iff_right, List.cons_append]
      rw [ih]
      simp

theorem wCell_succ (l : Fin r) (c : Fin r → ℂ) :
    wCell k r l.succ c = wCell k r l.castSucc c * w1 k r l (c l) := by
  simp only [wCell, Fin.val_succ, Fin.coe_castSucc]
  rw [filter_succ l, List.map_append, List.prod_append]
  simp

theorem wCell_zero (c : Fin r → ℂ) : wCell k r 0 c = 1 := by
  simp [wCell]

theorem wCell_congr {i : Fin (r + 1)} {c c' : Fin r → ℂ} (h : ∀ a : Fin r, a.val < i.val → c a = c' a) :
    wCell k r i c = wCell k r i c' := by
  unfold wCell
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [List.mem_filter] at ha
  rw [h a (by simpa using ha.2)]

def gam (k r : ℕ) (i : Fin (r + 1)) (c : Fin r → ℂ) : ℝ :=
  ∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1)

theorem gam_succ (l : Fin r) (c : Fin r → ℂ) :
    gam k r l.succ c = gam k r l.castSucc c * ‖c l‖ ^ (Mdim k r l - 1) := by
  have key : ∀ a : Fin r, (if a.val < l.succ.val then ‖c a‖ ^ (Mdim k r a - 1) else (1 : ℝ)) =
      (if a.val < l.castSucc.val then ‖c a‖ ^ (Mdim k r a - 1) else 1) *
        (if a = l then ‖c a‖ ^ (Mdim k r a - 1) else 1) := by
    intro a
    rw [Fin.val_succ, Fin.coe_castSucc]
    by_cases h1 : a = l
    · subst h1
      simp
    · have h3 : a.val ≠ l.val := fun h => h1 (Fin.ext h)
      by_cases h2 : a.val < l.val
      · rw [if_pos (show a.val < l.val + 1 by omega), if_pos h2, if_neg h1, mul_one]
      · rw [if_neg (show ¬ a.val < l.val + 1 by omega), if_neg h2, if_neg h1, mul_one]
  unfold gam
  rw [Finset.prod_congr rfl (fun a _ => key a), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Res (k r : ℕ) (l : Fin r) (Ψ : Fn k r E) : Fn k r E :=
  fun c g => ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • Ψ c (w1 k r l (c l) * g)

theorem resG_succ (l : Fin r) (F : Mx k r → E) : resG k r l.succ F = Res k r l (resG k r l.castSucc F) := by
  funext c g
  have hg := gam_succ (k := k) l c
  simp only [gam] at hg
  simp only [resG, Res, wCell_succ, hg, mul_assoc, smul_smul]
  congr 1
  push_cast
  ring

theorem resG_zero (F : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) : resG k r 0 F c g = F g := by
  simp [resG, wCell_zero]

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem cd_entries {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {A : X → Mx k r} :
    ContDiffOn ℝ ∞ A s ↔ ∀ p q, ContDiffOn ℝ ∞ (fun x => A x p q) s := by
  refine contDiffOn_pi.trans ?_
  exact forall_congr' fun p => contDiffOn_pi

theorem cd_matmul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {A B : X → Mx k r}
    (hA : ContDiffOn ℝ ∞ A s) (hB : ContDiffOn ℝ ∞ B s) : ContDiffOn ℝ ∞ (fun x => A x * B x) s := by
  rw [cd_entries] at hA hB ⊢
  intro p q
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun j _ => (hA p j).mul (hB j q)

theorem contDiffOn_weyl_cell (l : Fin r) : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => w1 k r l (c l)) (OmX r) := by
  rw [cd_entries]
  intro p q
  unfold w1
  split_ifs
  · exact (Qx3.cd_coord l).contDiffOn
  · exact (Qx3.cd_coordBar l).contDiffOn.inv (fun x hx => star_ne_zero.2 (hx l))
  · exact contDiffOn_const
  · exact contDiffOn_const

def mL (k r : ℕ) (l : Fin r) (x : XX k r) : XX k r := (x.1, w1 k r l (x.1 l) * x.2)

theorem cd_mL (l : Fin r) : ContDiffOn ℝ ∞ (mL k r l) {x : XX k r | x.1 ∈ OmX r} := by
  refine contDiff_fst.contDiffOn.prodMk (cd_matmul ?_ contDiff_snd.contDiffOn)
  exact (contDiffOn_weyl_cell l).comp contDiff_fst.contDiffOn (fun x hx => hx)

theorem cd_gamma (l : Fin r) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => ((‖c l‖ ^ n : ℝ) : ℂ)) (OmX r) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (((Qx3.cd_coord l).contDiffOn.norm ℝ (fun x (hx : x ∈ OmX r) => hx l)).pow n)

def UU (Dc : (Fin r → ℂ) → Set (Mx k r)) : Set (XX k r) := {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1}

def stepD (l : Fin r) (Dc : (Fin r → ℂ) → Set (Mx k r)) : (Fin r → ℂ) → Set (Mx k r) :=
  fun c => {g | w1 k r l (c l) * g ∈ Dc c}

def Dcell (D : Set (Mx k r)) (i : Fin (r + 1)) : (Fin r → ℂ) → Set (Mx k r) :=
  fun c => {g | wCell k r i c * g ∈ D}

theorem open_step (l : Fin r) {Dc : (Fin r → ℂ) → Set (Mx k r)} (h : IsOpen (UU Dc)) :
    IsOpen (UU (stepD l Dc)) := by
  have hO : IsOpen {x : XX k r | x.1 ∈ OmX r} := by
    have e : OmX r = ⋂ j : Fin r, {x : Fin r → ℂ | x j ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply j) continuous_const).preimage continuous_fst
  have e2 : UU (stepD l Dc) = {x : XX k r | x.1 ∈ OmX r} ∩ mL k r l ⁻¹' UU Dc := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact And.intro h1 (And.intro h1 h2)
    · rintro ⟨h1, -, h2⟩
      exact And.intro h1 h2
  rw [e2]
  exact (cd_mL (k := k) l).continuousOn.isOpen_inter_preimage hO h

theorem Dcell_succ (D : Set (Mx k r)) (l : Fin r) : Dcell D l.succ = stepD l (Dcell D l.castSucc) := by
  funext c
  ext g
  show wCell k r l.succ c * g ∈ D ↔ wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D
  rw [wCell_succ, mul_assoc]

theorem open_const {D : Set (Mx k r)} (hD : IsOpen D) : IsOpen (UU (fun _ : Fin r → ℂ => D)) := by
  have hO : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l : Fin r, {x : Fin r → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  exact hO.prod hD

theorem Dcell_zero (D : Set (Mx k r)) : Dcell D (0 : Fin (r + 1)) = fun _ => D := by
  funext c
  ext g
  show wCell k r 0 c * g ∈ D ↔ g ∈ D
  rw [wCell_zero, one_mul]

theorem open_Dcell {D : Set (Mx k r)} (hD : IsOpen D) (i : Fin (r + 1)) : IsOpen (UU (Dcell D i)) := by
  induction i using Fin.induction with
  | zero =>
    rw [Dcell_zero]
    exact open_const hD
  | succ l ih =>
    rw [Dcell_succ]
    exact open_step l ih

theorem Dcell_congr (D : Set (Mx k r)) {i : Fin (r + 1)} {c c' : Fin r → ℂ}
    (h : ∀ a : Fin r, a.val < i.val → c a = c' a) : Dcell D i c = Dcell D i c' := by
  ext g
  show wCell k r i c * g ∈ D ↔ wCell k r i c' * g ∈ D
  rw [wCell_congr h]

section Fam
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mul_mem_of_mem_inv_mul_ideal (hW : WeylLevelElementFacts) (l : Fin r) {c : ℂ} (hc : c ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g ∈ Glev k r l.castSucc :=
  Qx3.glev_mul (hW k r l c hc).1 (((hW k r l c hc).2 g hg).1)

theorem smooth_family_restriction (hW : WeylLevelElementFacts) (l : Fin r) {U U' : Set (XX k r)} {Φ : Fn k r E}
    (h : SmoothFam k r l.castSucc U Φ) (hU' : ∀ x ∈ U', x.1 ∈ OmX r ∧ mL k r l x ∈ U) :
    SmoothFam k r l.succ U' (fun c g => Φ c (w1 k r l (c l) * g)) := by
  intro x₀ hx₀ hg₀
  obtain ⟨hc₀, hm₀⟩ := hU' x₀ hx₀
  obtain ⟨V, F, hV, hxV, hF, hΦ⟩ := h (mL k r l x₀) hm₀ (mul_mem_of_mem_inv_mul_ideal hW l (hc₀ l) hg₀)
  refine ⟨{x : XX k r | x.1 ∈ OmX r} ∩ mL k r l ⁻¹' V, fun x => F (mL k r l x),
    (cd_mL (k := k) l).continuousOn.isOpen_inter_preimage Qx3.isOpen_OmXX hV, ⟨hc₀, hxV⟩, ?_, ?_⟩
  · exact hF.comp ((cd_mL l).mono Set.inter_subset_left) (fun x hx => hx.2)
  · intro x hx hxG
    exact hΦ (mL k r l x) hx.2 (mul_mem_of_mem_inv_mul_ideal hW l (hx.1 l) hxG)

theorem sf_Res (hW : WeylLevelElementFacts) (l : Fin r) {Dc : (Fin r → ℂ) → Set (Mx k r)} {Φ : Fn k r E}
    (h : SmoothFam k r l.castSucc (UU Dc) Φ) : SmoothFam k r l.succ (UU (stepD l Dc)) (Res k r l Φ) :=
  Qx3.sf_smul (Qx3.sf_ofC (cd_gamma l _) (fun _ hx => hx.1))
    (smooth_family_restriction hW l h (fun _ hx => ⟨hx.1, hx.1, hx.2⟩))

end Fam

section FF
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem ff_zero (i : Fin (r + 1)) (D : Set (Mx k r)) :
    (fun _ => 0 : Mx k r → (Wq →L[ℂ] Wp)) ∈ FFl k r z z' π π' i D := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  · intro g _ n _
    simp
  · intro g _ n _
    simp
  · intro g _ h _ h' _
    simp

theorem dom_step (hR : ResMem) (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r) {D : Set (Mx k r)}
    (hD : IsDom k r z z' l.castSucc D) {c : ℂ} (hc : c ≠ 0) :
    IsDom k r z z' l.succ {g | w1 k r l c * g ∈ D} :=
  (((hR ℂ ℂ k r z z' (fun _ => 0) (fun _ => 0) l D hz hz' hD _ (ff_zero _ _)).1) c hc).1

theorem dom_Dcell (hR : ResMem) (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)}
    (hD : IsDom k r z z' 0 D) (i : Fin (r + 1)) : ∀ c ∈ OmX r, IsDom k r z z' i (Dcell D i c) := by
  intro c hc
  induction i using Fin.induction with
  | zero =>
    rw [Dcell_zero]
    exact hD
  | succ l ih =>
    rw [Dcell_succ]
    exact dom_step hR hz hz' l ih ((show ∀ a, c a ≠ 0 from hc) l)

end FF

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Dir
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem add_smul_single (c : Fin r → ℂ) (a : Fin r) (v : ℂ) (t : ℝ) :
    c + t • (Pi.single a v : Fin r → ℂ) = Function.update c a (c a + t • v) := by
  funext j
  by_cases h : j = a
  · subst h
    simp
  · simp [h]

theorem fderiv_dir (a : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (κ : ℂ)
    (h1 : DifferentiableAt ℝ f₁ c) (h2 : DifferentiableAt ℝ f₂ c)
    (hev : ∀ᶠ s in 𝓝 (c a), f₁ (Function.update c a s) = κ • f₂ (Function.update c a s)) (v : ℂ) :
    fderiv ℝ f₁ c (Pi.single a v) = κ • fderiv ℝ f₂ c (Pi.single a v) := by
  have l1 : HasDerivAt (fun t : ℝ => f₁ (c + t • (Pi.single a v : Fin r → ℂ))) (fderiv ℝ f₁ c (Pi.single a v)) 0 :=
    h1.hasFDerivAt.hasLineDerivAt _
  have l2 : HasDerivAt (fun t : ℝ => f₂ (c + t • (Pi.single a v : Fin r → ℂ))) (fderiv ℝ f₂ c (Pi.single a v)) 0 :=
    h2.hasFDerivAt.hasLineDerivAt _
  have ht : Tendsto (fun t : ℝ => c a + t • v) (𝓝 0) (𝓝 (c a)) := by
    have : Continuous (fun t : ℝ => c a + t • v) := by fun_prop
    simpa using this.tendsto 0
  have ev : (fun t : ℝ => f₁ (c + t • (Pi.single a v : Fin r → ℂ))) =ᶠ[𝓝 0]
      fun t : ℝ => κ • f₂ (c + t • (Pi.single a v : Fin r → ℂ)) := by
    filter_upwards [ht.eventually hev] with t h
    rw [add_smul_single]
    exact h
  exact l1.unique ((l2.const_smul κ).congr_of_eventuallyEq ev)

theorem opL_dir (a : Fin r) (j : Fin 6) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (κ : ℂ)
    (h1 : DifferentiableAt ℝ f₁ c) (h2 : DifferentiableAt ℝ f₂ c)
    (hev : ∀ᶠ s in 𝓝 (c a), f₁ (Function.update c a s) = κ • f₂ (Function.update c a s)) :
    opL a j f₁ c = κ • opL a j f₂ c := by
  have h0 : f₁ c = κ • f₂ c := by simpa using hev.self_of_nhds
  have hfd := fderiv_dir a κ h1 h2 hev
  fin_cases j
  · show pOp a f₁ c = κ • pOp a f₂ c
    unfold pOp wirt
    split_ifs
    · simp only [hfd, smul_sub, smul_comm κ]
    · simp
  · show c a • f₁ c = κ • (c a • f₂ c)
    rw [h0, smul_comm]
  · show (c a)⁻¹ • f₁ c = κ • ((c a)⁻¹ • f₂ c)
    rw [h0, smul_comm]
  · show pbOp a f₁ c = κ • pbOp a f₂ c
    unfold pbOp wirtBar
    split_ifs
    · simp only [hfd, smul_add, smul_comm κ]
    · simp
  · show star (c a) • f₁ c = κ • (star (c a) • f₂ c)
    rw [h0, smul_comm]
  · show (star (c a))⁻¹ • f₁ c = κ • ((star (c a))⁻¹ • f₂ c)
    rw [h0, smul_comm]

theorem opL_germ (a : Fin r) (j : Fin 6) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (hev : f₁ =ᶠ[𝓝 c] f₂) :
    opL a j f₁ c = opL a j f₂ c := by
  have h0 : f₁ c = f₂ c := hev.self_of_nhds
  have hfd : fderiv ℝ f₁ c = fderiv ℝ f₂ c := hev.fderiv_eq
  fin_cases j
  · show pOp a f₁ c = pOp a f₂ c
    unfold pOp wirt
    rw [hfd]
  · show c a • f₁ c = c a • f₂ c
    rw [h0]
  · show (c a)⁻¹ • f₁ c = (c a)⁻¹ • f₂ c
    rw [h0]
  · show pbOp a f₁ c = pbOp a f₂ c
    unfold pbOp wirtBar
    rw [hfd]
  · show star (c a) • f₁ c = star (c a) • f₂ c
    rw [h0]
  · show (star (c a))⁻¹ • f₁ c = (star (c a))⁻¹ • f₂ c
    rw [h0]

theorem opL_lin (a : Fin r) (j : Fin 6) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (s : ℂ)
    (h1 : DifferentiableAt ℝ f₁ c) (h2 : DifferentiableAt ℝ f₂ c) :
    opL a j (fun x => f₁ x + s • f₂ x) c = opL a j f₁ c + s • opL a j f₂ c := by
  have hfd : ∀ v, fderiv ℝ (fun x => f₁ x + s • f₂ x) c v = fderiv ℝ f₁ c v + s • fderiv ℝ f₂ c v := by
    intro v
    have h : HasFDerivAt (fun x => f₁ x + s • f₂ x) (fderiv ℝ f₁ c + s • fderiv ℝ f₂ c) c :=
      h1.hasFDerivAt.add (h2.hasFDerivAt.const_smul s)
    rw [h.fderiv]
    rfl
  fin_cases j
  · show pOp a _ c = pOp a f₁ c + s • pOp a f₂ c
    unfold pOp wirt
    split_ifs
    · simp only [hfd, smul_sub, smul_add, smul_comm s]
      abel
    · simp
  · show c a • (f₁ c + s • f₂ c) = c a • f₁ c + s • (c a • f₂ c)
    rw [smul_add, smul_comm]
  · show (c a)⁻¹ • (f₁ c + s • f₂ c) = (c a)⁻¹ • f₁ c + s • ((c a)⁻¹ • f₂ c)
    rw [smul_add, smul_comm]
  · show pbOp a _ c = pbOp a f₁ c + s • pbOp a f₂ c
    unfold pbOp wirtBar
    split_ifs
    · simp only [hfd, smul_add, smul_comm s]
      abel
    · simp
  · show star (c a) • (f₁ c + s • f₂ c) = star (c a) • f₁ c + s • (star (c a) • f₂ c)
    rw [smul_add, smul_comm]
  · show (star (c a))⁻¹ • (f₁ c + s • f₂ c) = (star (c a))⁻¹ • f₁ c + s • ((star (c a))⁻¹ • f₂ c)
    rw [smul_add, smul_comm]

theorem opL_shift (a : Fin r) (j : Fin 6) {f : (Fin r → ℂ) → E} {c c' : Fin r → ℂ} (hc : c ∈ OmX r)
    (hc' : c' ∈ OmX r) (ha : c a = c' a) (hev : ∀ᶠ x in 𝓝 c', f x = f (x + (c - c'))) :
    opL a j f c = opL a j f c' := by
  have h0 : f c' = f c := by simpa using hev.self_of_nhds
  have hfd : fderiv ℝ f c' = fderiv ℝ f c := by
    have e : f =ᶠ[𝓝 c'] fun x => f (x + (c - c')) := hev
    rw [e.fderiv_eq, fderiv_comp_add_right]
    simp
  fin_cases j
  · show pOp a f c = pOp a f c'
    unfold pOp wirt
    rw [if_pos hc, if_pos hc', hfd, ha]
  · show c a • f c = c' a • f c'
    rw [h0, ha]
  · show (c a)⁻¹ • f c = (c' a)⁻¹ • f c'
    rw [h0, ha]
  · show pbOp a f c = pbOp a f c'
    unfold pbOp wirtBar
    rw [if_pos hc, if_pos hc', hfd, ha]
  · show star (c a) • f c = star (c' a) • f c'
    rw [h0, ha]
  · show (star (c a))⁻¹ • f c = (star (c' a))⁻¹ • f c'
    rw [h0, ha]

end Dir

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

structure LinRel {X : Type*} [AddCommGroup X] [Module ℂ X] (R : X → X → Prop) : Prop where
  zero : R 0 0
  add : ∀ {a b a' b'}, R a b → R a' b' → R (a + a') (b + b')
  smul : ∀ (s : ℂ) {a b}, R a b → R (s • a) (s • b)

theorem LinRel.neg {X : Type*} [AddCommGroup X] [Module ℂ X] {R : X → X → Prop} (h : LinRel R) {a b : X}
    (hab : R a b) : R (-a) (-b) := by
  simpa using h.smul (-1) hab

theorem LinRel.sub {X : Type*} [AddCommGroup X] [Module ℂ X] {R : X → X → Prop} (h : LinRel R) {a b a' b' : X}
    (hab : R a b) (hab' : R a' b') : R (a - a') (b - b') := by
  simpa [sub_eq_add_neg] using h.add hab (h.neg hab')

def Pres2 {X : Type*} (R : X → X → Prop) (T T' : X → X) : Prop := ∀ a b, R a b → R (T a) (T' b)

section OM
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem preserves_transfer_letter {R : Fn k r E → Fn k r E → Prop} (hR : LinRel R) (l : Fin r)
    (h : ∀ q, Pres2 R (crd (opL l q)) (crd (opL l q))) (Y : ℂ) (a b : Fin 2) :
    Pres2 R (TL k l Y a b) (TL k l Y a b) := by
  intro Φ Ψ hΦ
  fin_cases a <;> fin_cases b
  · exact hR.add (hR.smul Y hΦ) (h 0 _ _ hΦ)
  · exact hR.neg (h 1 _ _ hΦ)
  · exact h 2 _ _ hΦ
  · exact hR.zero

theorem preserves_transfer_letter_star {R : Fn k r E → Fn k r E → Prop} (hR : LinRel R) (l : Fin r)
    (h : ∀ q, Pres2 R (crd (opL l q)) (crd (opL l q))) (Y : ℂ) (a b : Fin 2) :
    Pres2 R (TLs k l Y a b) (TLs k l Y a b) := by
  intro Φ Ψ hΦ
  fin_cases a <;> fin_cases b
  · exact hR.sub (hR.smul Y hΦ) (h 3 _ _ hΦ)
  · exact h 5 _ _ hΦ
  · exact hR.neg (h 4 _ _ hΦ)
  · exact hR.zero

theorem preserves_operator_mul {X : Type*} [AddCommGroup X] [Module ℂ X] {R : X → X → Prop} (hR : LinRel R) {M M' N N' : OM X}
    (hM : ∀ a b, Pres2 R (M a b) (M' a b)) (hN : ∀ a b, Pres2 R (N a b) (N' a b)) (a b : Fin 2) :
    Pres2 R (oMul M N a b) (oMul M' N' a b) := by
  intro x y hxy
  simp only [oMul, Fin.sum_univ_two]
  exact hR.add (hM a 0 _ _ (hN 0 b x y hxy)) (hM a 1 _ _ (hN 1 b x y hxy))

theorem preserves_sandwich {R : Fn k r E → Fn k r E → Prop} (hR : LinRel R) (Y : ℂ) : ∀ (j : ℕ)
    (_ : ∀ l : Fin r, l.val < j → ∀ q, Pres2 R (crd (opL l q)) (crd (opL l q))) {M M' : OM (Fn k r E)}
    (_ : ∀ a b, Pres2 R (M a b) (M' a b)) (a b : Fin 2), Pres2 R (sandw k r Y j M a b) (sandw k r Y j M' a b)
  | 0, _, _, _, hM, a, b => hM a b
  | j + 1, h, M, M', hM, a, b => by
    show Pres2 R (sandw k r Y j _ a b) (sandw k r Y j _ a b)
    refine preserves_sandwich hR Y j (fun l hl => h l (Nat.lt_succ_of_lt hl)) ?_ a b
    intro a b
    by_cases hj : j < r
    · simp only [dif_pos hj]
      exact preserves_operator_mul hR (preserves_transfer_letter_star hR _ (h ⟨j, hj⟩ (Nat.lt_succ_self j)) Y)
        (preserves_operator_mul hR hM (preserves_transfer_letter hR _ (h ⟨j, hj⟩ (Nat.lt_succ_self j)) Y)) a b
    · simp only [dif_neg hj]
      exact hM a b

end OM

section FF
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem ff_add {i : Fin (r + 1)} {D : Set (Mx k r)} {J J' : Mx k r → (Wq →L[ℂ] Wp)}
    (h : J ∈ FFl k r z z' π π' i D) (h' : J' ∈ FFl k r z z' π π' i D) : J + J' ∈ FFl k r z z' π π' i D := by
  obtain ⟨hs, hl, hr, he⟩ := h
  obtain ⟨hs', hl', hr', he'⟩ := h'
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hs g₀ hg₀
    obtain ⟨U', F', hU', hgU', hF', hFe'⟩ := hs' g₀ hg₀
    refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', Set.mem_inter hgU hgU',
      (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
    show J g + J' g = F g + F' g
    rw [hFe g hg.1 hgl, hFe' g hg.2 hgl]
  · intro g hg n hn
    simp only [Pi.add_apply]
    rw [hl g hg n hn, hl' g hg n hn, smul_add]
  · intro g hg n hn
    simp only [Pi.add_apply]
    rw [hr g hg n hn, hr' g hg n hn, smul_add]
  · intro g hg x hx x' hx'
    simp only [Pi.add_apply]
    rw [he g hg x hx x' hx', he' g hg x hx x' hx', ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

theorem ff_smul {i : Fin (r + 1)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} (s : ℂ)
    (h : J ∈ FFl k r z z' π π' i D) : s • J ∈ FFl k r z z' π π' i D := by
  obtain ⟨hs, hl, hr, he⟩ := h
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hs g₀ hg₀
    refine ⟨U, fun g => s • F g, hU, hgU, hF.const_smul s, fun g hg hgl => ?_⟩
    show s • J g = s • F g
    rw [hFe g hg hgl]
  · intro g hg n hn
    simp only [Pi.smul_apply]
    rw [hl g hg n hn, smul_comm]
  · intro g hg n hn
    simp only [Pi.smul_apply]
    rw [hr g hg n hn, smul_comm]
  · intro g hg x hx x' hx'
    simp only [Pi.smul_apply]
    rw [he g hg x hx x' hx', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

variable {L : Fin (r + 1)} {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)}

theorem fam_zero : FamFF k r z z' π π' L Dc 0 := by
  refine And.intro ?_ ?_
  · intro x₀ _ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  · intro c _
    exact ff_zero L (Dc c)

theorem fam_add {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' L Dc Φ) (h' : FamFF k r z z' π π' L Dc Ψ) :
    FamFF k r z z' π π' L Dc (Φ + Ψ) := by
  obtain ⟨hs, hf⟩ := h
  obtain ⟨hs', hf'⟩ := h'
  refine And.intro ?_ ?_
  · intro x₀ hx₀ hg
    obtain ⟨U, F, hU, hxU, hF, hFe⟩ := hs x₀ hx₀ hg
    obtain ⟨U', F', hU', hxU', hF', hFe'⟩ := hs' x₀ hx₀ hg
    refine ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', Set.mem_inter hxU hxU',
      (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun x hx hxg => ?_⟩
    show Φ x.1 x.2 + Ψ x.1 x.2 = F x + F' x
    rw [hFe x hx.1 hxg, hFe' x hx.2 hxg]
  · intro c hc
    exact ff_add (hf c hc) (hf' c hc)

theorem fam_smul (s : ℂ) {Φ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' L Dc Φ) :
    FamFF k r z z' π π' L Dc (s • Φ) := by
  obtain ⟨hs, hf⟩ := h
  refine And.intro ?_ ?_
  · intro x₀ hx₀ hg
    obtain ⟨U, F, hU, hxU, hF, hFe⟩ := hs x₀ hx₀ hg
    refine ⟨U, fun x => s • F x, hU, hxU, hF.const_smul s, fun x hx hxg => ?_⟩
    show s • Φ x.1 x.2 = s • F x
    rw [hFe x hx hxg]
  · intro c hc
    exact ff_smul s (hf c hc)

theorem fam_QL (hTP : TPreservesFF) (hz : inWb k r z) (hz' : inWb k r z')
    (hd : ∀ c ∈ OmX r, IsDom k r z z' L (Dc c)) (Y : ℂ) (a b : Fin 2) {Φ : Fn k r (Wq →L[ℂ] Wp)}
    (h : FamFF k r z z' π π' L Dc Φ) : FamFF k r z z' π π' L Dc (QL k r z z' L Y a b Φ) :=
  ⟨Qx3.pres_tL z z' Y a b Φ h.1,
    fun c hc => hTP Wp Wq k r z z' π π' L (Dc c) Y a b hz hz' (hd c hc) (Φ c) (h.2 c hc)⟩

theorem fam_diff {Φ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' L Dc Φ) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c) : DifferentiableAt ℝ (fun c' => Φ c' g) c := by
  obtain ⟨hs, -⟩ := h
  obtain ⟨U, F, hU, hxU, hF, hFe⟩ := hs (c, g) (And.intro hc hgD) hg
  have hpair : DifferentiableAt ℝ (fun c' : Fin r → ℂ => ((c', g) : (Fin r → ℂ) × Mx k r)) c := by fun_prop
  have h1 : DifferentiableAt ℝ F (c, g) := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (fun c' => F (c', g)) c := h1.comp c hpair
  refine hd.congr_of_eventuallyEq ?_
  have hcont : Continuous (fun c' : Fin r → ℂ => ((c', g) : (Fin r → ℂ) × Mx k r)) := by fun_prop
  have hev : ∀ᶠ c' in 𝓝 c, ((c', g) : (Fin r → ℂ) × Mx k r) ∈ U := hcont.continuousAt.eventually_mem (hU.mem_nhds hxU)
  exact hev.mono fun c' hc' => hFe (c', g) hc' hg

variable (z z' π π') in

def RS (L : Fin (r + 1)) (Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)) (S : Set (Fin r → ℂ))
    (Φ Ψ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  FamFF k r z z' π π' L Dc Φ ∧ FamFF k r z z' π π' L Dc₀ Ψ ∧
    ∀ c ∈ S, ∀ g ∈ Glev k r L, g ∈ Dc c → Φ c g = Ψ c g

variable (z z') in
structure SData (L : Fin (r + 1)) (Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)) (S : Set (Fin r → ℂ)) : Prop where
  o : IsOpen (UU Dc)
  o₀ : IsOpen (UU Dc₀)
  d : ∀ c ∈ OmX r, IsDom k r z z' L (Dc c)
  d₀ : ∀ c ∈ OmX r, IsDom k r z z' L (Dc₀ c)
  sub : S ⊆ OmX r
  eq : ∀ c ∈ S, Dc c = Dc₀ c

variable {S : Set (Fin r → ℂ)}

theorem RS_lin : LinRel (RS z z' π π' L Dc Dc₀ S) where
  zero := ⟨fam_zero, fam_zero, fun _ _ _ _ _ => rfl⟩
  add := fun h h' => ⟨fam_add h.1 h'.1, fam_add h.2.1 h'.2.1, fun c hc g hg hgD => by
    simp only [Pi.add_apply, h.2.2 c hc g hg hgD, h'.2.2 c hc g hg hgD]⟩
  smul := fun s _ _ h => ⟨fam_smul s h.1, fam_smul s h.2.1, fun c hc g hg hgD => by
    simp only [Pi.smul_apply, h.2.2 c hc g hg hgD]⟩

theorem near_update {Dc : (Fin r → ℂ) → Set (Mx k r)} (ho : IsOpen (UU Dc)) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hgD : g ∈ Dc c) (l : Fin r) :
    ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ OmX r ∧ g ∈ Dc (Function.update c l s) := by
  have hmem : ((c, g) : XX k r) ∈ UU Dc := And.intro hc hgD
  have hcont2 : Continuous (fun c' : Fin r → ℂ => ((c', g) : XX k r)) := by fun_prop
  have h1 : ∀ᶠ c' in 𝓝 c, c' ∈ OmX r ∧ g ∈ Dc c' := hcont2.continuousAt.eventually_mem (ho.mem_nhds hmem)
  have hcont : Continuous (fun s : ℂ => Function.update c l s) := by
    first
      | exact continuous_const.update l continuous_id
      | fun_prop
      | exact (continuous_update l).comp (continuous_const.prodMk continuous_id)
  have ht : Filter.Tendsto (fun s : ℂ => Function.update c l s) (𝓝 (c l)) (𝓝 c) := by
    simpa using hcont.tendsto (c l)
  exact ht.eventually h1

theorem near_pt {Dc : (Fin r → ℂ) → Set (Mx k r)} (ho : IsOpen (UU Dc)) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hgD : g ∈ Dc c) : ∀ᶠ c' in 𝓝 c, c' ∈ OmX r ∧ g ∈ Dc c' := by
  have hmem : ((c, g) : XX k r) ∈ UU Dc := And.intro hc hgD
  have hcont : Continuous (fun c' : Fin r → ℂ => ((c', g) : XX k r)) := by fun_prop
  exact hcont.continuousAt.eventually_mem (ho.mem_nhds hmem)

theorem RS_op (hFO : FamOps) (hz : inWb k r z) (hz' : inWb k r z') (hS : SData z z' L Dc Dc₀ S) (l : Fin r)
    (hSl : ∀ c ∈ S, ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ S) (q : Fin 6) :
    Pres2 (RS z z' π π' L Dc Dc₀ S) (crd (opL l q)) (crd (opL l q)) := by
  intro Φ Ψ h
  refine ⟨hFO Wp Wq k r z z' π π' L Dc Φ hz hz' hS.o h.1 l q, hFO Wp Wq k r z z' π π' L Dc₀ Ψ hz hz' hS.o₀ h.2.1 l q,
    ?_⟩
  intro c hc g hg hgD
  have hcΩ := hS.sub hc
  have := opL_dir l q (f₁ := fun c' => Φ c' g) (f₂ := fun c' => Ψ c' g) (c := c) 1
    (fam_diff h.1 hcΩ hg hgD) (fam_diff h.2.1 hcΩ hg (hS.eq c hc ▸ hgD))
    (by
      filter_upwards [hSl c hc, near_update hS.o hcΩ hgD l] with s hs1 hs2
      rw [one_smul]
      exact h.2.2 _ hs1 g hg hs2.2)
  rw [one_smul] at this
  exact this

theorem RS_QL (hTP : TPreservesFF) (hLL : TLinLoc) (hz : inWb k r z) (hz' : inWb k r z')
    (hS : SData z z' L Dc Dc₀ S) (Y : ℂ) (a b : Fin 2) :
    Pres2 (RS z z' π π' L Dc Dc₀ S) (QL k r z z' L Y a b) (QL k r z z' L Y a b) := by
  intro Φ Ψ h
  refine ⟨fam_QL hTP hz hz' hS.d Y a b h.1, fam_QL hTP hz hz' hS.d₀ Y a b h.2.1, ?_⟩
  intro c hc g hg hgD
  have hcΩ := hS.sub hc
  have h2 : SmoothLev k r L (Dc c) (Ψ c) := by
    rw [hS.eq c hc]
    exact (h.2.1.2 c hcΩ).1
  exact ((hLL _ k r z z' L (Dc c) Y a b (Φ c) (Ψ c) 0 (hS.d c hcΩ).1 (h.1.2 c hcΩ).1 h2 g ⟨hg, hgD⟩).2)
    (fun x hx => h.2.2 c hc x hx.1 hx.2)

end FF

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section Ind
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Ind (i : ℕ) (Φ : Fn k r E) : Prop :=
  ∀ c ∈ OmX r, ∀ c' ∈ OmX r, (∀ a : Fin r, a.val < i → c a = c' a) → Φ c = Φ c'

theorem ind_op {i : ℕ} (j : Fin r) (hj : j.val < i) (q : Fin 6) {Φ : Fn k r E} (h : Ind i Φ) :
    Ind i (crd (opL j q) Φ) := by
  intro c hc c' hc' hcc
  funext g
  refine opL_shift j q hc hc' (hcc j hj) ?_
  have hcont : Continuous (fun x : Fin r → ℂ => x + (c - c')) := by fun_prop
  have h1 : ∀ᶠ x in 𝓝 c', x + (c - c') ∈ OmX r :=
    hcont.continuousAt.preimage_mem_nhds ((Qx3.isOpen_OmX r).mem_nhds (by simpa using hc))
  filter_upwards [h1, (Qx3.isOpen_OmX r).mem_nhds hc'] with x hx1 hx2
  rw [h x hx2 _ hx1 (fun a ha => by simp [hcc a ha])]

theorem ind_QL {i : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (L : Fin (r + 1)) (Y : ℂ) (a b : Fin 2) {Φ : Fn k r E}
    (h : Ind i Φ) : Ind i (QL k r z z' L Y a b Φ) := by
  intro c hc c' hc' hcc
  show tL k r z z' L Y a b (Φ c) = tL k r z z' L Y a b (Φ c')
  rw [h c hc c' hc' hcc]

theorem ind_resG (i : Fin (r + 1)) (J : Mx k r → E) : Ind i.val (resG k r i J) := by
  intro c _ c' _ h
  funext g
  have hp : (∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1 : ℝ)) =
      ∏ a : Fin r, (if a.val < i.val then ‖c' a‖ ^ (Mdim k r a - 1) else 1 : ℝ) := by
    refine Finset.prod_congr rfl (fun a _ => ?_)
    by_cases ha : a.val < i.val
    · simp [ha, h a ha]
    · simp [ha]
  simp only [resG, hp, wCell_congr h]

theorem update_mem_Om {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) {s : ℂ} (hs : s ≠ 0) :
    Function.update c l s ∈ OmX r := by
  show ∀ a, Function.update c l s a ≠ 0
  intro a
  by_cases h : a = l
  · subst h
    simpa using hs
  · simpa [h] using (show ∀ a, c a ≠ 0 from hc) a

theorem ev_ne {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) : ∀ᶠ s in 𝓝 (c l), s ≠ 0 := by
  exact eventually_ne_nhds ((show ∀ a, c a ≠ 0 from hc) l)

end Ind

section Chain
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fam_Res (hW : WeylLevelElementFacts) (hR : ResMem) (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r)
    {Dc : (Fin r → ℂ) → Set (Mx k r)} (hd : ∀ c ∈ OmX r, IsDom k r z z' l.castSucc (Dc c))
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' l.castSucc Dc Φ) :
    FamFF k r z z' π π' l.succ (stepD l Dc) (Res k r l Φ) :=
  ⟨sf_Res hW l h.1, fun c hc => ff_smul _
    ((((hR Wp Wq k r z z' π π' l (Dc c) hz hz' (hd c hc) (Φ c) (h.2 c hc)).1) (c l) (hc l)).2)⟩

theorem sdata_self (hR : ResMem) (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D)
    (i : Fin (r + 1)) : SData z z' i (Dcell D i) (Dcell D i) (OmX r) := by
  have ho : IsOpen D := (show IsOpen D ∧ _ from hD).1
  exact ⟨open_Dcell ho i, open_Dcell ho i, dom_Dcell hR hz hz' hD i, dom_Dcell hR hz hz' hD i,
    subset_rfl, fun _ _ => rfl⟩

theorem om_stable (l : Fin r) : ∀ c ∈ OmX r, ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ OmX r := by
  intro c hc
  exact (ev_ne hc l).mono fun s hs => update_mem_Om hc l hs

def stepOp (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (Y : ℂ) : OM (Fn k r (Wq →L[ℂ] Wp)) :=
  oMul (TLs k l Y) (oMul (QL k r z z' l.succ Y) (TL k l Y))

theorem RS_stepOp (hFO : FamOps) (hTP : TPreservesFF) (hLL : TLinLoc) (hz : inWb k r z) (hz' : inWb k r z')
    (l : Fin r) {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)} {S : Set (Fin r → ℂ)} (hS : SData z z' l.succ Dc Dc₀ S)
    (hSl : ∀ c ∈ S, ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ S) (Y : ℂ) (a b : Fin 2) :
    Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (stepOp z z' l Y a b) (stepOp z z' l Y a b) := by
  have hl : LinRel (RS z z' π π' l.succ Dc Dc₀ S) := RS_lin
  have h1 : ∀ a b, Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (TLs k l Y a b) (TLs k l Y a b) :=
    preserves_transfer_letter_star hl l (RS_op hFO hz hz' hS l hSl) Y
  have h2 : ∀ a b, Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (TL k l Y a b) (TL k l Y a b) :=
    preserves_transfer_letter hl l (RS_op hFO hz hz' hS l hSl) Y
  have h3 : ∀ a b, Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (QL k r z z' l.succ Y a b) (QL k r z z' l.succ Y a b) :=
    RS_QL hTP hLL hz hz' hS Y
  have h4 : ∀ a b, Pres2 (RS z z' π π' l.succ Dc Dc₀ S) (oMul (QL k r z z' l.succ Y) (TL k l Y) a b)
      (oMul (QL k r z z' l.succ Y) (TL k l Y) a b) :=
    preserves_operator_mul (M := QL k r z z' l.succ Y) (M' := QL k r z z' l.succ Y) (N := TL k l Y) (N' := TL k l Y) hl h3 h2
  exact preserves_operator_mul (M := TLs k l Y) (M' := TLs k l Y) (N := oMul (QL k r z z' l.succ Y) (TL k l Y))
    (N' := oMul (QL k r z z' l.succ Y) (TL k l Y)) hl h1 h4 a b

theorem step_fam (hCS : ChainStep) (hR : ResMem) (hFO : FamOps) (hTP : TPreservesFF) (hLL : TLinLoc) (hW : WeylLevelElementFacts)
    (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D) (l : Fin r) (Y : ℂ)
    (a b : Fin 2) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamFF k r z z' π π' l.castSucc (Dcell D l.castSucc) Φ)
    (hI : Ind l.val Φ) {c₀ : Fin r → ℂ} (hc₀ : c₀ ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r l.succ)
    (hgD : g ∈ Dcell D l.succ c₀) :
    stepOp z z' l Y a b (Res k r l Φ) c₀ g = Res k r l (QL k r z z' l.castSucc Y a b Φ) c₀ g := by
  set D' := Dcell D l.castSucc c₀ with hD'
  have hdom' : IsDom k r z z' l.castSucc D' := dom_Dcell hR hz hz' hD _ c₀ hc₀
  set S : Set (Fin r → ℂ) := {c | c ∈ OmX r ∧ ∀ a : Fin r, a.val < l.val → c a = c₀ a} with hSdef
  have hS : SData z z' l.succ (Dcell D l.succ) (stepD l (fun _ => D')) S := by
    refine ⟨open_Dcell hD.1 _, open_step l (open_const hdom'.1), dom_Dcell hR hz hz' hD _,
      fun c hc => dom_step hR hz hz' l hdom' (hc l), fun c hc => hc.1, ?_⟩
    intro c hc
    rw [Dcell_succ]
    show {g | w1 k r l (c l) * g ∈ Dcell D l.castSucc c} = {g | w1 k r l (c l) * g ∈ D'}
    rw [hD', Dcell_congr D (i := l.castSucc) (c := c) (c' := c₀) (fun a ha => hc.2 a ha)]
  have hSl : ∀ c ∈ S, ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ S := by
    intro c hc
    filter_upwards [ev_ne hc.1 l] with s hs
    refine ⟨update_mem_Om hc.1 l hs, fun a ha => ?_⟩
    have hne : a ≠ l := fun e => by rw [e] at ha; exact lt_irrefl _ ha
    rw [Function.update_of_ne hne]
    exact hc.2 a ha
  have hJ₀ := hΦ.2 c₀ hc₀
  have hrel : RS z z' π π' l.succ (Dcell D l.succ) (stepD l (fun _ => D')) S (Res k r l Φ) (res1 k r l (Φ c₀)) := by
    refine ⟨?_, (hR Wp Wq k r z z' π π' l D' hz hz' hdom' (Φ c₀) hJ₀).2, ?_⟩
    · rw [Dcell_succ]
      exact fam_Res hW hR hz hz' l (dom_Dcell hR hz hz' hD _) hΦ
    · intro c hc x _ _
      show _ • Φ c _ = _ • Φ c₀ _
      rw [hI c hc.1 c₀ hc₀ hc.2]
  have h1 := (RS_stepOp hFO hTP hLL hz hz' l hS hSl Y a b _ _ hrel).2.2 c₀ ⟨hc₀, fun _ _ => rfl⟩ g hg hgD
  rw [h1]
  have hgD' : w1 k r l (c₀ l) * g ∈ D' := by
    rw [Dcell_succ] at hgD
    exact hgD
  exact (hCS Wp Wq k r z z' π π' l D' Y a b hz hz' hdom' (Φ c₀) hJ₀ c₀ hc₀ g hg hgD').symm

variable (z z' π π') in

def RK (D : Set (Mx k r)) (l : Fin r) (Φ Ψ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  FamFF k r z z' π π' l.castSucc (Dcell D l.castSucc) Φ ∧ Ind l.val Φ ∧
    FamFF k r z z' π π' l.succ (Dcell D l.succ) Ψ ∧
    ∀ c ∈ OmX r, ∀ g ∈ Glev k r l.succ, g ∈ Dcell D l.succ c → Ψ c g = Res k r l Φ c g

theorem RK_lin (D : Set (Mx k r)) (l : Fin r) : LinRel (RK z z' π π' D l) where
  zero := ⟨fam_zero, fun _ _ _ _ _ => rfl, fam_zero, fun _ _ _ _ _ => by simp [Res]⟩
  add := fun h h' => ⟨fam_add h.1 h'.1, fun c hc c' hc' hcc => by
      simp only [Pi.add_apply, h.2.1 c hc c' hc' hcc, h'.2.1 c hc c' hc' hcc],
    fam_add h.2.2.1 h'.2.2.1, fun c hc g hg hgD => by
      simp only [Pi.add_apply, h.2.2.2 c hc g hg hgD, h'.2.2.2 c hc g hg hgD, Res, smul_add]⟩
  smul := fun s _ _ h => ⟨fam_smul s h.1, fun c hc c' hc' hcc => by
      simp only [Pi.smul_apply, h.2.1 c hc c' hc' hcc],
    fam_smul s h.2.2.1, fun c hc g hg hgD => by
      simp only [Pi.smul_apply, h.2.2.2 c hc g hg hgD, Res, smul_comm s]⟩

theorem RK_op (hR : ResMem) (hFO : FamOps) (hW : WeylLevelElementFacts) (hz : inWb k r z) (hz' : inWb k r z')
    {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D) (l j : Fin r) (hj : j.val < l.val) (q : Fin 6) :
    Pres2 (RK z z' π π' D l) (crd (opL j q)) (crd (opL j q)) := by
  intro Φ Ψ h
  refine ⟨hFO Wp Wq k r z z' π π' _ _ Φ hz hz' (open_Dcell hD.1 _) h.1 j q, ind_op j hj q h.2.1,
    hFO Wp Wq k r z z' π π' _ _ Ψ hz hz' (open_Dcell hD.1 _) h.2.2.1 j q, ?_⟩
  intro c hc g hg hgD
  have hne : l ≠ j := fun e => by rw [e] at hj; exact lt_irrefl _ hj
  have e1 : opL j q (fun c' => Ψ c' g) c = opL j q (fun c' => Res k r l Φ c' g) c := by
    apply opL_germ
    filter_upwards [near_pt (open_Dcell hD.1 l.succ) hc hgD] with c' hc'
    exact h.2.2.2 c' hc'.1 g hg hc'.2
  have hRes : FamFF k r z z' π π' l.succ (Dcell D l.succ) (Res k r l Φ) := by
    rw [Dcell_succ]
    exact fam_Res hW hR hz hz' l (dom_Dcell hR hz hz' hD _) h.1
  have hgD' : w1 k r l (c l) * g ∈ Dcell D l.castSucc c := by
    rw [Dcell_succ] at hgD
    exact hgD
  have e2 := opL_dir j q (f₁ := fun c' => Res k r l Φ c' g) (f₂ := fun c' => Φ c' (w1 k r l (c l) * g)) (c := c)
    ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) (fam_diff hRes hc hg hgD)
    (fam_diff h.1 hc (mul_mem_of_mem_inv_mul_ideal hW l (hc l) hg) hgD')
    (Filter.Eventually.of_forall fun s => by
      show _ • Φ _ _ = _
      rw [Function.update_of_ne hne])
  exact e1.trans e2

theorem RK_QL (hCS : ChainStep) (hR : ResMem) (hFO : FamOps) (hTP : TPreservesFF) (hLL : TLinLoc) (hW : WeylLevelElementFacts)
    (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D) (l : Fin r) (Y : ℂ)
    (a b : Fin 2) : Pres2 (RK z z' π π' D l) (QL k r z z' l.castSucc Y a b) (stepOp z z' l Y a b) := by
  intro Φ Ψ h
  have hRes : FamFF k r z z' π π' l.succ (Dcell D l.succ) (Res k r l Φ) := by
    rw [Dcell_succ]
    exact fam_Res hW hR hz hz' l (dom_Dcell hR hz hz' hD _) h.1
  have h2 := RS_stepOp (π := π) (π' := π') hFO hTP hLL hz hz' l (sdata_self hR hz hz' hD l.succ) (om_stable l) Y a b
    Ψ (Res k r l Φ) ⟨h.2.2.1, hRes, h.2.2.2⟩
  refine ⟨fam_QL hTP hz hz' (dom_Dcell hR hz hz' hD _) Y a b h.1, ind_QL z z' _ Y a b h.2.1, h2.1, ?_⟩
  intro c hc g hg hgD
  rw [h2.2.2 c hc g hg hgD]
  exact step_fam hCS hR hFO hTP hLL hW hz hz' hD l Y a b h.1 h.2.1 hc hg hgD

theorem chainAll_of (hCS : ChainStep) (hR : ResMem) (hRG : ResGFam) (hFO : FamOps) (hTP : TPreservesFF)
    (hLL : TLinLoc) (hW : WeylLevelElementFacts) : ChainAll := by
  intro Wp Wq _ _ _ _ k r z z' π π' i D Y a b hz hz' hD J hJ
  induction i using Fin.induction generalizing a b with
  | zero =>
    intro c _ g _ _
    have e : resG k r 0 J c = J := funext fun x => resG_zero J c x
    show resG k r 0 _ c g = tL k r z z' 0 Y a b (resG k r 0 J c) g
    rw [resG_zero, e]
  | succ l ih =>
    intro c hc g hg hgD
    have h0 : RK z z' π π' D l (resG k r l.castSucc J) (resG k r l.succ J) :=
      ⟨hRG Wp Wq k r z z' π π' D hz hz' hD J hJ _, ind_resG l.castSucc J, hRG Wp Wq k r z z' π π' D hz hz' hD J hJ _,
        fun c _ g _ _ => by rw [resG_succ]⟩
    have h1 := preserves_sandwich (R := RK z z' π π' D l) (RK_lin D l) Y l.val
      (fun j hj q => RK_op hR hFO hW hz hz' hD l j hj q)
      (M := QL k r z z' l.castSucc Y) (M' := stepOp z z' l Y)
      (fun a b => RK_QL hCS hR hFO hTP hLL hW hz hz' hD l Y a b) a b _ _ h0
    have h2 := h1.2.2.2 c hc g hg hgD
    have e : sandw k r Y l.succ.val (QL k r z z' l.succ Y) =
        sandw k r Y l.val (stepOp (Wp := Wp) (Wq := Wq) z z' l Y) := by
      show sandw k r Y (l.val + 1) _ = _
      show sandw k r Y l.val _ = _
      rw [dif_pos l.isLt]
      rfl
    rw [e, h2, resG_succ]
    show _ • _ = _ • _
    congr 1
    have hgD' : wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D := by
      have : wCell k r l.succ c * g ∈ D := hgD
      rwa [wCell_succ, Matrix.mul_assoc] at this
    exact ih a b c hc _ (mul_mem_of_mem_inv_mul_ideal hW l (hc l) hg) hgD'

end Chain

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z :=
  ⟨WeylGroupFacts.uh_one, fun _ => ⟨by simp, by simp⟩, by simp⟩

theorem one_nlev (i : Fin (r + 1)) : (1 : Mx k r) ∈ Nlev k r i := ⟨WeylGroupFacts.mem_n_one, Qx3.glev_one i⟩

section Dom
variable {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem dom_left (hD : IsDom k r z z' i D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) {n : Mx k r}
    (hn : n ∈ Nlev k r i) : n * g ∈ Glev k r i ∩ D := by
  have := hD.2 g hg (1 * n) ⟨1, one_uw z, n, hn, rfl⟩ (1 * 1) ⟨1, one_uw z', 1, one_nlev i, rfl⟩
  exact ⟨Qx3.glev_mul hn.2 hg.1, by simpa using this⟩

theorem dom_right (hD : IsDom k r z z' i D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) {n : Mx k r}
    (hn : n ∈ Nlev k r i) : g * n ∈ Glev k r i ∩ D := by
  have := hD.2 g hg (1 * 1) ⟨1, one_uw z, 1, one_nlev i, rfl⟩ (1 * n) ⟨1, one_uw z', n, hn, rfl⟩
  exact ⟨Qx3.glev_mul hg.1 hn.2, by simpa using this⟩

theorem dom_uw (hD : IsDom k r z z' i D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) {h h' : Mx k r}
    (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') : h * g * h' ∈ Glev k r i ∩ D := by
  have := hD.2 g hg (h * 1) ⟨h, hh, 1, one_nlev i, rfl⟩ (h' * 1) ⟨h', hh', 1, one_nlev i, rfl⟩
  exact ⟨Qx3.glev_mul (Qx3.glev_mul (Qx3.uw_glev i hh) hg.1) (Qx3.uw_glev i hh'), by simpa using this⟩

theorem smooth_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (hD : IsOpen D) {f f' : Mx k r → E}
    (h : SmoothLev k r i D f) (he : ∀ g ∈ Glev k r i ∩ D, f' g = f g) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hf⟩ := h g₀ hg₀
  exact ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left,
    fun g hg hgG => (he g ⟨hgG, hg.2⟩).trans (hf g hg.1 hgG)⟩

end Dom

section Cut
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}

open Classical in

def cutP (L : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Mx k r)) : Fn k r E →ₗ[ℂ] Fn k r E where
  toFun := fun Φ c g => if c ∈ OmX r ∧ g ∈ Glev k r L ∧ g ∈ Dc c then Φ c g else 0
  map_add' := fun Φ Ψ => by
    funext c g
    by_cases h : c ∈ OmX r ∧ g ∈ Glev k r L ∧ g ∈ Dc c <;> simp [h]
  map_smul' := fun s Φ => by
    funext c g
    by_cases h : c ∈ OmX r ∧ g ∈ Glev k r L ∧ g ∈ Dc c <;> simp [h]

theorem cutP_on (Φ : Fn k r E) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r L)
    (hgD : g ∈ Dc c) : cutP L Dc Φ c g = Φ c g := by
  simp [cutP, hc, hg, hgD]

theorem cutP_eq_iff (Φ Ψ : Fn k r E) :
    cutP L Dc Φ = cutP L Dc Ψ ↔ ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → Φ c g = Ψ c g := by
  constructor
  · intro h c hc g hg hgD
    have h1 := congrFun (congrFun h c) g
    rwa [cutP_on Φ hc hg hgD, cutP_on Ψ hc hg hgD] at h1
  · intro h
    funext c g
    by_cases hh : c ∈ OmX r ∧ g ∈ Glev k r L ∧ g ∈ Dc c
    · rw [cutP_on Φ hh.1 hh.2.1 hh.2.2, cutP_on Ψ hh.1 hh.2.1 hh.2.2]
      exact h c hh.1 g hh.2.1 hh.2.2
    · simp only [cutP, LinearMap.coe_mk, AddHom.coe_mk, if_neg hh]

def mkData (L : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Mx k r)) (P : Fn k r E → Prop) (h0 : P 0)
    (hadd : ∀ Φ Ψ, P Φ → P Ψ → P (Φ + Ψ)) (hsmul : ∀ (s : ℂ) Φ, P Φ → P (s • Φ))
    (hN : ∀ Φ, P Φ → P (cutP L Dc Φ)) : HatData (Fn k r E) where
  G := { carrier := {Φ | P Φ}
         zero_mem' := h0
         add_mem' := fun h h' => hadd _ _ h h'
         smul_mem' := fun s _ h => hsmul s _ h }
  N := cutP L Dc
  N_mem := hN
  N_idem := fun Φ => (cutP_eq_iff _ _).2 (fun _ hc _ hg hgD => cutP_on Φ hc hg hgD)

end Cut

section FF
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem ff_congr {i : Fin (r + 1)} {D : Set (Mx k r)} (hD : IsDom k r z z' i D) {J J' : Mx k r → (Wq →L[ℂ] Wp)}
    (h : J ∈ FFl k r z z' π π' i D) (he : ∀ g ∈ Glev k r i ∩ D, J' g = J g) : J' ∈ FFl k r z z' π π' i D := by
  refine ⟨smooth_congr hD.1 h.1 he, ?_, ?_, ?_⟩
  · intro g hg n hn
    rw [he g hg, he _ (dom_left hD hg hn)]
    exact h.2.1 g hg n hn
  · intro g hg n hn
    rw [he g hg, he _ (dom_right hD hg hn)]
    exact h.2.2.1 g hg n hn
  · intro g hg a ha b hb
    rw [he g hg, he _ (dom_uw hD hg ha hb)]
    exact h.2.2.2 g hg a ha b hb

variable {L : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}

theorem fam_congr (hS : SData z z' L Dc Dc (OmX r)) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)}
    (h : FamFF k r z z' π π' L Dc Φ) (he : ∀ c ∈ OmX r, ∀ g ∈ Glev k r L, g ∈ Dc c → Ψ c g = Φ c g) :
    FamFF k r z z' π π' L Dc Ψ :=
  ⟨Qx3.sf_congr_on hS.o (fun _ hx => hx) (fun x hx hxG => he x.1 hx.1 x.2 hxG hx.2) h.1,
    fun c hc => ff_congr (hS.d c hc) (h.2 c hc) (fun g hg => he c hc g hg.1 hg.2)⟩

variable (π π') in

def famData (hS : SData z z' L Dc Dc (OmX r)) : HatData (Fn k r (Wq →L[ℂ] Wp)) :=
  mkData (E := Wq →L[ℂ] Wp) L Dc (FamFF k r z z' π π' L Dc) fam_zero (fun _ _ h h' => fam_add h h')
    (fun s _ h => fam_smul s h) (fun Φ h => fam_congr hS h (fun _ hc _ hg hgD => cutP_on Φ hc hg hgD))

theorem good_of (hS : SData z z' L Dc Dc (OmX r)) {T : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)}
    (hP : Pres2 (RS z z' π π' L Dc Dc (OmX r)) T T)
    (hl : ∀ Φ Ψ, FamFF k r z z' π π' L Dc Φ → FamFF k r z z' π π' L Dc Ψ → ∀ s : ℂ, ∀ c ∈ OmX r,
      ∀ g ∈ Glev k r L, g ∈ Dc c → T (Φ + s • Ψ) c g = T Φ c g + s • T Ψ c g) :
    (famData π π' hS).Good T where
  mem := fun Φ h => (hP Φ Φ ⟨h, h, fun _ _ _ _ _ => rfl⟩).1
  congr := fun Φ h Ψ h' he => (cutP_eq_iff _ _).2 (hP Φ Ψ ⟨h, h', (cutP_eq_iff _ _).1 he⟩).2.2
  lin := fun Φ h Ψ h' s => by
    show cutP L Dc _ = cutP L Dc _ + s • cutP L Dc _
    rw [← map_smul, ← map_add]
    exact (cutP_eq_iff _ _).2 (hl Φ Ψ h h' s)

theorem good_op (hFO : FamOps) (hz : inWb k r z) (hz' : inWb k r z') (hS : SData z z' L Dc Dc (OmX r))
    (l : Fin r) (q : Fin 6) : (famData π π' hS).Good (crd (opL l q)) := by
  refine good_of hS (RS_op hFO hz hz' hS l (om_stable l) q) ?_
  intro Φ Ψ hΦ hΨ s c hc g hg hgD
  exact opL_lin l q s (fam_diff hΦ hc hg hgD) (fam_diff hΨ hc hg hgD)

theorem good_QL (hTP : TPreservesFF) (hLL : TLinLoc) (hz : inWb k r z) (hz' : inWb k r z')
    (hS : SData z z' L Dc Dc (OmX r)) (Y : ℂ) (a b : Fin 2) : (famData π π' hS).Good (QL k r z z' L Y a b) :=
  good_of hS (RS_QL hTP hLL hz hz' hS Y a b) (fun Φ Ψ h h' s c hc g hg hgD =>
    (hLL _ k r z z' L (Dc c) Y a b (Φ c) (Ψ c) s (hS.d c hc).1 (h.2 c hc).1 (h'.2 c hc).1 g ⟨hg, hgD⟩).1)

end FF

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section HatM
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)

def hatM (M : OM X) : Matrix (Fin 2) (Fin 2) (Module.End ℂ H.V) := fun a b => H.hat (M a b)

variable {H}

theorem oMul_eq (M N : OM X) (a b : Fin 2) : oMul M N a b = fun f => M a 0 (N 0 b f) + M a 1 (N 1 b f) := by
  funext f
  simp [oMul, Fin.sum_univ_two]

theorem good_oMul {M N : OM X} (hM : ∀ a b, H.Good (M a b)) (hN : ∀ a b, H.Good (N a b)) (a b : Fin 2) :
    H.Good (oMul M N a b) := by
  rw [oMul_eq]
  exact ((hM a 0).comp (hN 0 b)).add ((hM a 1).comp (hN 1 b))

theorem hatM_oMul {M N : OM X} (hM : ∀ a b, H.Good (M a b)) (hN : ∀ a b, H.Good (N a b)) :
    hatM H (oMul M N) = hatM H M * hatM H N := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  show H.hat (oMul M N a b) = H.hat (M a 0) * H.hat (N 0 b) + H.hat (M a 1) * H.hat (N 1 b)
  rw [oMul_eq, HatData.hat_add ((hM a 0).comp (hN 0 b)) ((hM a 1).comp (hN 1 b)), HatData.hat_comp (hM a 0) (hN 0 b),
    HatData.hat_comp (hM a 1) (hN 1 b)]

end HatM

section CV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (H : HatData (Fn k r E))

variable {H} in
theorem good_TL (hop : ∀ l q, H.Good (crd (opL l q))) (l : Fin r) (Y : ℂ) (a b : Fin 2) : H.Good (TL k l Y a b) := by
  fin_cases a <;> fin_cases b
  · exact (HatData.good_id.smul Y).add (hop l 0)
  · exact (hop l 1).neg
  · exact hop l 2
  · exact HatData.good_zero

variable {H} in
theorem good_TLs (hop : ∀ l q, H.Good (crd (opL l q))) (l : Fin r) (Y : ℂ) (a b : Fin 2) :
    H.Good (TLs k l Y a b) := by
  fin_cases a <;> fin_cases b
  · exact (HatData.good_id.smul Y).sub (hop l 3)
  · exact hop l 5
  · exact (hop l 4).neg
  · exact HatData.good_zero

def Rp (Y : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) (Module.End ℂ H.V)
  | 0 => 1
  | j + 1 => (if h : j < r then hatM H (TL k ⟨j, h⟩ Y) else 1) * Rp Y j

def Lp (Y : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) (Module.End ℂ H.V)
  | 0 => 1
  | j + 1 => Lp Y j * (if h : j < r then hatM H (TLs k ⟨j, h⟩ Y) else 1)

variable {H}

theorem sandw_hat (hop : ∀ l q, H.Good (crd (opL l q))) (Y : ℂ) : ∀ (j : ℕ) (M : OM (Fn k r E)),
    (∀ a b, H.Good (M a b)) →
    (∀ a b, H.Good (sandw k r Y j M a b)) ∧ hatM H (sandw k r Y j M) = Lp H Y j * hatM H M * Rp H Y j
  | 0, M, hM => ⟨hM, by simp [sandw, Lp, Rp]⟩
  | j + 1, M, hM => by
    by_cases hj : j < r
    · have e : sandw k r Y (j + 1) M = sandw k r Y j (oMul (TLs k ⟨j, hj⟩ Y) (oMul M (TL k ⟨j, hj⟩ Y))) := by
        show sandw k r Y j _ = _
        rw [dif_pos hj]
      have g1 := good_oMul hM (good_TL hop ⟨j, hj⟩ Y)
      have g2 := good_oMul (good_TLs hop ⟨j, hj⟩ Y) g1
      obtain ⟨h1, h2⟩ := sandw_hat hop Y j _ g2
      rw [e]
      refine ⟨h1, ?_⟩
      rw [h2, hatM_oMul (good_TLs hop ⟨j, hj⟩ Y) g1, hatM_oMul hM (good_TL hop ⟨j, hj⟩ Y)]
      simp only [Lp, Rp, dif_pos hj, Matrix.mul_assoc]
    · have e : sandw k r Y (j + 1) M = sandw k r Y j M := by
        show sandw k r Y j _ = _
        rw [dif_neg hj]
      obtain ⟨h1, h2⟩ := sandw_hat hop Y j M hM
      rw [e]
      refine ⟨h1, ?_⟩
      rw [h2]
      simp only [Lp, Rp, dif_neg hj, Matrix.mul_one, Matrix.one_mul]

theorem vAB_hat (hop : ∀ l q, H.Good (crd (opL l q))) (Y : ℂ) : ∀ (j : ℕ) (b : Fin 2),
    H.Good (crd (cmp (vAB (E := E) r Y j) b)) ∧ H.hat (crd (cmp (vAB (E := E) r Y j) b)) = Rp H Y j b 0
  | 0, b => by
    fin_cases b
    · exact ⟨HatData.good_id, HatData.hat_id⟩
    · exact ⟨HatData.good_zero, HatData.hat_zero⟩
  | j + 1, b => by
    obtain ⟨gA, hA⟩ := vAB_hat hop Y j 0
    obtain ⟨gB, hB⟩ := vAB_hat hop Y j 1
    by_cases hj : j < r
    · have ev : vAB (E := E) r Y (j + 1) =
          (fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) - cOp ⟨j, hj⟩ ((vAB r Y j).2 f),
            fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) := by
        show (if h : j < r then _ else _) = _
        rw [dif_pos hj]
      have hR : Rp H Y (j + 1) = hatM H (TL k ⟨j, hj⟩ Y) * Rp H Y j := by
        simp only [Rp, dif_pos hj]
      have gT := good_TL hop ⟨j, hj⟩ Y
      rw [hR, ev]
      have key0 : H.Good (crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0)) ∧
          H.hat (crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0)) =
            (hatM H (TL k ⟨j, hj⟩ Y) * Rp H Y j) 0 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, ← hA, ← hB]
        have e : crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0) =
            fun Φ : Fn k r E => TL k ⟨j, hj⟩ Y 0 0 (crd (cmp (vAB (E := E) r Y j) 0) Φ) +
              TL k ⟨j, hj⟩ Y 0 1 (crd (cmp (vAB (E := E) r Y j) 1) Φ) := by
          funext Φ c g
          exact sub_eq_add_neg _ _
        rw [e]
        exact ⟨((gT 0 0).comp gA).add ((gT 0 1).comp gB), by
          rw [HatData.hat_add ((gT 0 0).comp gA) ((gT 0 1).comp gB), HatData.hat_comp (gT 0 0) gA,
            HatData.hat_comp (gT 0 1) gB]
          rfl⟩
      have key1 : H.Good (crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1)) ∧
          H.hat (crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1)) =
            (hatM H (TL k ⟨j, hj⟩ Y) * Rp H Y j) 1 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, ← hA, ← hB]
        have e : crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1) =
            fun Φ : Fn k r E => TL k ⟨j, hj⟩ Y 1 0 (crd (cmp (vAB (E := E) r Y j) 0) Φ) := rfl
        rw [e]
        refine ⟨(gT 1 0).comp gA, ?_⟩
        have h11 : hatM H (TL k ⟨j, hj⟩ Y) 1 1 = 0 := HatData.hat_zero
        rw [HatData.hat_comp (gT 1 0) gA, h11, zero_mul, add_zero]
        rfl
      fin_cases b
      · exact key0
      · exact key1
    · have ev : vAB (E := E) r Y (j + 1) = vAB r Y j := by
        show (if h : j < r then _ else _) = _
        rw [dif_neg hj]
      have hR : Rp H Y (j + 1) = Rp H Y j := by
        simp only [Rp, dif_neg hj, Matrix.one_mul]
      rw [ev, hR]
      exact vAB_hat hop Y j b

theorem vABs_hat (hop : ∀ l q, H.Good (crd (opL l q))) (Y : ℂ) : ∀ (j : ℕ) (a : Fin 2),
    H.Good (crd (cmp (vABs (E := E) r Y j) a)) ∧ H.hat (crd (cmp (vABs (E := E) r Y j) a)) = Lp H Y j 0 a
  | 0, a => by
    fin_cases a
    · exact ⟨HatData.good_id, HatData.hat_id⟩
    · exact ⟨HatData.good_zero, HatData.hat_zero⟩
  | j + 1, a => by
    obtain ⟨gA, hA⟩ := vABs_hat hop Y j 0
    obtain ⟨gB, hB⟩ := vABs_hat hop Y j 1
    by_cases hj : j < r
    · have ev : vABs (E := E) r Y (j + 1) =
          (fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) := by
        show (if h : j < r then _ else _) = _
        rw [dif_pos hj]
      have hL : Lp H Y (j + 1) = Lp H Y j * hatM H (TLs k ⟨j, hj⟩ Y) := by
        simp only [Lp, dif_pos hj]
      have gT := good_TLs hop ⟨j, hj⟩ Y
      rw [hL, ev]
      have key0 : H.Good (crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0)) ∧
          H.hat (crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0)) = (Lp H Y j * hatM H (TLs k ⟨j, hj⟩ Y)) 0 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, ← hA, ← hB]
        have e : crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0) =
            fun Φ : Fn k r E => crd (cmp (vABs (E := E) r Y j) 0) (TLs k ⟨j, hj⟩ Y 0 0 Φ) -
              crd (cmp (vABs (E := E) r Y j) 1) (crd (opL ⟨j, hj⟩ 4) Φ) := rfl
        rw [e]
        refine ⟨(gA.comp (gT 0 0)).sub (gB.comp (hop _ 4)), ?_⟩
        have h10 : hatM H (TLs k ⟨j, hj⟩ Y) 1 0 = -H.hat (crd (opL ⟨j, hj⟩ 4)) := HatData.hat_neg (hop _ 4)
        rw [HatData.hat_sub (gA.comp (gT 0 0)) (gB.comp (hop _ 4)), HatData.hat_comp gA (gT 0 0),
          HatData.hat_comp gB (hop _ 4), h10, mul_neg, ← sub_eq_add_neg]
        rfl
      have key1 : H.Good (crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1)) ∧
          H.hat (crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1)) = (Lp H Y j * hatM H (TLs k ⟨j, hj⟩ Y)) 0 1 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, ← hA, ← hB]
        have e : crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1) =
            fun Φ : Fn k r E => crd (cmp (vABs (E := E) r Y j) 0) (TLs k ⟨j, hj⟩ Y 0 1 Φ) := rfl
        rw [e]
        refine ⟨gA.comp (gT 0 1), ?_⟩
        have h11 : hatM H (TLs k ⟨j, hj⟩ Y) 1 1 = 0 := HatData.hat_zero
        rw [HatData.hat_comp gA (gT 0 1), h11, mul_zero, add_zero]
        rfl
      fin_cases a
      · exact key0
      · exact key1
    · have ev : vABs (E := E) r Y (j + 1) = vABs r Y j := by
        show (if h : j < r then _ else _) = _
        rw [dif_neg hj]
      have hL : Lp H Y (j + 1) = Lp H Y j := by
        simp only [Lp, dif_neg hj, Matrix.mul_one]
      rw [ev, hL]
      exact vABs_hat hop Y j a

theorem rc_eq (hop : ∀ l q, H.Good (crd (opL l q))) (Y : ℂ) (j : ℕ) (M : OM (Fn k r E))
    (hM : ∀ a b, H.Good (M a b)) {Φ : Fn k r E} (hΦ : Φ ∈ H.G) :
    H.N (sandw k r Y j M 0 0 Φ) =
      H.N (∑ a : Fin 2, ∑ b : Fin 2, crd (cmp (vABs r Y j) a) (M a b (crd (cmp (vAB r Y j) b) Φ))) := by
  obtain ⟨g1, h1⟩ := sandw_hat hop Y j M hM
  have gv := fun b => (vAB_hat (H := H) hop Y j b).1
  have hv := fun b => (vAB_hat (H := H) hop Y j b).2
  have gs := fun a => (vABs_hat (H := H) hop Y j a).1
  have hs := fun a => (vABs_hat (H := H) hop Y j a).2
  have gt : ∀ a b, H.Good (fun Φ => crd (cmp (vABs (E := E) r Y j) a) (M a b (crd (cmp (vAB r Y j) b) Φ))) :=
    fun a b => (gs a).comp ((hM a b).comp (gv b))
  have ht : ∀ a b, H.hat (fun Φ => crd (cmp (vABs (E := E) r Y j) a) (M a b (crd (cmp (vAB r Y j) b) Φ))) =
      Lp H Y j 0 a * (hatM H M a b * Rp H Y j b 0) := by
    intro a b
    rw [HatData.hat_comp (gs a) ((hM a b).comp (gv b)), HatData.hat_comp (hM a b) (gv b), hs, hv]
    rfl
  have gW := ((gt 0 0).add (gt 0 1)).add ((gt 1 0).add (gt 1 1))
  have hW : H.hat (sandw k r Y j M 0 0) = H.hat (fun Φ =>
      (crd (cmp (vABs (E := E) r Y j) 0) (M 0 0 (crd (cmp (vAB r Y j) 0) Φ)) +
        crd (cmp (vABs (E := E) r Y j) 0) (M 0 1 (crd (cmp (vAB r Y j) 1) Φ))) +
      (crd (cmp (vABs (E := E) r Y j) 1) (M 1 0 (crd (cmp (vAB r Y j) 0) Φ)) +
        crd (cmp (vABs (E := E) r Y j) 1) (M 1 1 (crd (cmp (vAB r Y j) 1) Φ)))) := by
    rw [HatData.hat_add ((gt 0 0).add (gt 0 1)) ((gt 1 0).add (gt 1 1)), HatData.hat_add (gt 0 0) (gt 0 1),
      HatData.hat_add (gt 1 0) (gt 1 1), ht, ht, ht, ht]
    have := congrFun (congrFun h1 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two] at this
    refine this.trans ?_
    noncomm_ring
  have h2 := congrArg (fun T => ((T (H.toV Φ hΦ) : H.V) : Fn k r E)) hW
  simp only [HatData.hat_toV (g1 0 0) hΦ, HatData.hat_toV gW hΦ] at h2
  simp only [Fin.sum_univ_two]
  exact h2

end CV

end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cVv_of (hCA : ChainAll) (hR : ResMem) (hRG : ResGFam) (hFO : FamOps) (hTP : TPreservesFF)
    (hLL : TLinLoc) : CVv := by
  intro Wp Wq _ _ _ _ k r z z' π π' i D Y hz hz' hD J hJ c hc g hg hgD
  have hS := sdata_self hR hz hz' hD i
  have h1 := hCA Wp Wq k r z z' π π' i D Y 0 0 hz hz' hD J hJ c hc g hg hgD
  have hop : ∀ l q, (famData π π' hS).Good (crd (opL l q)) := fun l q => good_op hFO hz hz' hS l q
  have hM : ∀ a b, (famData π π' hS).Good (QL k r z z' i Y a b) := fun a b => good_QL hTP hLL hz hz' hS Y a b
  have hΦ : resG k r i J ∈ (famData π π' hS).G := hRG Wp Wq k r z z' π π' D hz hz' hD J hJ i
  have h2 := rc_eq hop Y i.val (QL k r z z' i Y) hM hΦ
  have h3 := (cutP_eq_iff _ _).1 h2 c hc g hg hgD
  simp only [Fin.sum_univ_two] at h3 ⊢
  exact h1.trans h3

theorem chainFromStep : ChainFromStep := by
  intro hCS hR hRG hFO hTP hLL hW
  exact ⟨chainAll_of hCS hR hRG hFO hTP hLL hW, cVv_of (chainAll_of hCS hR hRG hFO hTP hLL hW) hR hRG hFO hTP hLL⟩

end

end Formalism.FourierDecayAlt.P.Qx6

namespace Formalism.FourierDecayAlt.P

theorem line_expansions_from_line_form : Formalism.FourierDecayAlt.Q.ExpRowsFromRowForm := by
  exact Qx6.expRows

theorem border_from_expansions : Formalism.FourierDecayAlt.Q.BorderFromExpansions := by
  exact Qx6.borderFromExpansions

theorem chain_recursion_from_single_descent : Formalism.FourierDecayAlt.Q.ChainFromStep := by
  exact Qx6.chainFromStep

end Formalism.FourierDecayAlt.P
