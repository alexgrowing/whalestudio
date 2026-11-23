import Formalism.HermitianCurvature.StatementWd

namespace Formalism.FourierDecayAlt.P.Wd6

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Units

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem cond_iff (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (x a = i ∧ y = Function.update x a j) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    funext b
    by_cases hb : b = a
    · subst hb; simp [h2]
    · simp [Function.update_of_ne hb, h3 b hb]
  · rintro ⟨h1, rfl⟩
    refine ⟨h1, by simp, ?_⟩
    intro b hb
    simp [Function.update_of_ne hb]

theorem eU_apply (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  unfold eU
  simp only [Matrix.of_apply]
  exact if_congr (cond_iff a i j x y) rfl rfl

theorem eU_mul_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((eU a i j : SlopeTestRemainingChoices S A) * B) x y = if x a = i then B (Function.update x a j) y else 0 := by
  rw [Matrix.mul_apply]
  simp only [eU_apply]
  by_cases h : x a = i
  · simp [h]
  · simp [h]

theorem eU_mul_eU (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [eU_mul_apply, eU_apply]
  by_cases hjk : j = k
  · subst hjk
    simp only [Function.update_self, Function.update_idem, true_and, if_true]
    rw [eU_apply]
    by_cases h : x a = i <;> simp [h]
  · simp [hjk]

theorem eU_comm_of_ne {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  rw [Function.update_of_ne (Ne.symm hc), Function.update_of_ne hc, Function.update_comm hc]
  by_cases h1 : x c = i <;> by_cases h2 : x a = k <;> simp [h1, h2]

theorem ins_free {a c : S} (hc : c ≠ a) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro i j
  unfold ins
  refine Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
  exact (eU_comm_of_ne hc i j k l).mul_right (hM k l i j)

theorem ins_comm (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) (hb : FreeOf a b)
    (hbM : ∀ i j, Commute b (M i j)) : Commute b (ins a M) := by
  unfold ins
  refine Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
  exact (hb k l).symm.mul_right (hbM k l)

end Units

def EC {B : Type} [Mul B] (z : B) (M : M2 B) : Prop := ∀ i j, Commute z (M i j)

section General

variable {B : Type} [Ring B]

theorem EC.mul {z : B} {M N : M2 B} (hM : EC z M) (hN : EC z N) : EC z (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun k _ => (hM i k).mul_right (hN k j)

theorem EC.one (z : B) : EC z (1 : M2 B) := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem EC.transpose {z : B} {M : M2 B} (hM : EC z M) : EC z Mᵀ := fun i j => hM j i

theorem diag_comm {z : B} {M : M2 B} (h : EC z M) :
    (Matrix.diagonal fun _ => z) * M = M * (Matrix.diagonal fun _ => z) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (h i j).eq

theorem transpose_mul_of_comm {M N : M2 B} (h : ∀ i j, EC (M i j) N) :
    (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (h j k k i).eq

theorem transpose_mul_diag (M : M2 B) (z : B) :
    (M * (Matrix.diagonal fun _ => z))ᵀ = Mᵀ * (Matrix.diagonal fun _ => z) := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.transpose_apply]

theorem transpose_diag_mul (M : M2 B) (z : B) :
    ((Matrix.diagonal fun _ => z) * M)ᵀ = (Matrix.diagonal fun _ => z) * Mᵀ := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.transpose_apply]

end General

section Slots

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by
  unfold io; exact map_mul _ x y

theorem io_sub (x y : A) : (io (x - y) : SlopeTestRemainingChoices S A) = io x - io y := by
  unfold io; exact map_sub _ x y

theorem io_smul (k : K) (x : A) : (io (k • x) : SlopeTestRemainingChoices S A) = k • io x := by
  unfold io
  ext X Y
  by_cases h : X = Y
  · subst h; simp
  · simp [h]

theorem eU_io (a : S) (i j : Fin 2) (x : A) : Commute (eU a i j : SlopeTestRemainingChoices S A) (io x) := by
  show (eU a i j : SlopeTestRemainingChoices S A) * io x = io x * eU a i j
  unfold io
  ext X Y
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU_apply]
  split_ifs <;> simp

theorem io_free (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := fun i j => eU_io a i j x

theorem io_comm {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  show (io x : SlopeTestRemainingChoices S A) * io y = io y * io x
  rw [← io_mul, ← io_mul, h.eq]

theorem diagScalar_mul (x y : SlopeTestRemainingChoices S A) : d0 (x * y) = d0 x * d0 y := by
  unfold d0
  rw [Matrix.diagonal_mul_diagonal]

theorem entry_commute_R_matrix {z : SlopeTestRemainingChoices S A} {a : S} (h : ∀ i j, Commute z (eU a i j)) (D : K) : EC z (Rh0 a D) := by
  intro i j
  unfold Rh0 P0
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply]
  exact Commute.smul_right (Commute.sub_right (Commute.smul_right (EC.one z i j) _) (h j i)) _

theorem entry_commute_transposed_R_matrix {z : SlopeTestRemainingChoices S A} {a : S} (h : ∀ i j, Commute z (eU a i j)) (D : K) : EC z (Rht0 a D) := by
  intro i j
  unfold Rht0 Q0
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply]
  exact Commute.smul_right (Commute.sub_right (Commute.smul_right (EC.one z i j) _) (h i j)) _

theorem Rh0_transpose (a : S) (D : K) : (Rh0 a D : M2 (SlopeTestRemainingChoices S A))ᵀ = Rht0 a D := by
  unfold Rh0 Rht0 P0 Q0
  ext i j
  simp [Matrix.one_apply, eq_comm]

end Slots

section Slots

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

def Rel (M N : M2 A) (D : K) : Prop :=
  ∀ i k r s, D • (M i k * N r s) - M r k * N i s = D • (N r s * M i k) - N r k * M i s

theorem unit_mul (a : S) (i j r s : Fin 2) (x y : A) :
    ((eU a i j : SlopeTestRemainingChoices S A) * io x) * (eU a r s * io y) = if j = r then eU a i s * io (x * y) else 0 := by
  calc ((eU a i j : SlopeTestRemainingChoices S A) * io x) * (eU a r s * io y)
      = eU a i j * (io x * eU a r s) * io y := by simp only [mul_assoc]
    _ = eU a i j * (eU a r s * io x) * io y := by rw [(eU_io a r s x).eq]
    _ = (eU a i j * eU a r s) * (io x * io y) := by simp only [mul_assoc]
    _ = _ := by rw [eU_mul_eU, ← io_mul]; split_ifs <;> simp

theorem io_mul_ins (a : S) (x : A) (N : M2 A) :
    (io x : SlopeTestRemainingChoices S A) * ins a (lift0 N) = ∑ r, ∑ s, eU a r s * io (x * N r s) := by
  unfold ins lift0
  simp only [Finset.mul_sum, Matrix.map_apply, io_mul]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, ← (eU_io a r s x).eq, mul_assoc]

theorem ins_mul_io (a : S) (x : A) (N : M2 A) :
    ins a (lift0 N) * (io x : SlopeTestRemainingChoices S A) = ∑ r, ∑ s, eU a r s * io (N r s * x) := by
  unfold ins lift0
  simp only [Finset.sum_mul, Matrix.map_apply, io_mul, mul_assoc]

theorem unit_mul_ins (a : S) (j i : Fin 2) (x : A) (N : M2 A) :
    (eU a j i : SlopeTestRemainingChoices S A) * io x * ins a (lift0 N) = ∑ s, eU a j s * io (x * N i s) := by
  unfold ins lift0
  simp only [Finset.mul_sum, Matrix.map_apply, unit_mul]
  simp

theorem ins_mul_unit (a : S) (k j : Fin 2) (x : A) (N : M2 A) :
    ins a (lift0 N) * (io x * (eU a k j : SlopeTestRemainingChoices S A)) = ∑ r, eU a r j * io (N r k * x) := by
  unfold ins lift0
  rw [← (eU_io a k j x).eq]
  simp only [Finset.sum_mul, Matrix.map_apply, unit_mul]
  simp

theorem shifted_flip_position_relation (a : S) (M N : M2 A) (D : K) (h : Rel M N D) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * lift0 M * d0 (ins a (lift0 N)) =
      d0 (ins a (lift0 N)) * lift0 M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by
  have L : ∀ i k, ((D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * lift0 M * d0 (ins a (lift0 N)) : M2 (SlopeTestRemainingChoices S A)) i k =
      ∑ r, ∑ s, eU a r s * io (D • (M i k * N r s) - M r k * N i s) := by
    intro i k
    unfold d0
    rw [Matrix.mul_diagonal, sub_mul, Matrix.sub_apply, smul_mul_assoc, one_mul, Matrix.smul_apply,
      sub_mul, smul_mul_assoc, Matrix.mul_apply]
    simp only [io_sub, io_smul, mul_sub, Finset.sum_sub_distrib, mul_smul_comm, ← Finset.smul_sum]
    congr 1
    · congr 1
      exact io_mul_ins a (M i k) N
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      exact unit_mul_ins a r i (M r k) N
  have Rr : ∀ i k, (d0 (ins a (lift0 N)) * lift0 M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) : M2 (SlopeTestRemainingChoices S A)) i k =
      ∑ r, ∑ s, eU a r s * io (D • (N r s * M i k) - N r k * M i s) := by
    intro i k
    unfold d0
    rw [mul_assoc, Matrix.diagonal_mul, mul_sub, Matrix.sub_apply, mul_smul_comm, mul_one, Matrix.smul_apply,
      mul_sub, mul_smul_comm, Matrix.mul_apply]
    simp only [io_sub, io_smul, mul_sub, Finset.sum_sub_distrib, mul_smul_comm, ← Finset.smul_sum]
    congr 1
    · congr 1
      exact ins_mul_io a (M i k) N
    · rw [Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      exact ins_mul_unit a k s (M i s) N
  ext1 i k
  rw [L, Rr]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [h i k r s]

theorem rtt_relation (a : S) (M N : M2 A) (D : K) (h : Rel M N D) :
    Rh0 a D * lift0 M * d0 (ins a (lift0 N)) = d0 (ins a (lift0 N)) * lift0 M * Rh0 a D := by
  unfold Rh0
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, shifted_flip_position_relation a M N D h]

theorem relT (p c ci : A) (D Y Y' : K) (h1 : D • (p * c) - D • (c * p) = (Y - Y') • c)
    (h2 : D • (p * ci) - D • (ci * p) = (Y' - Y) • ci) (h3 : c * ci = ci * c) :
    Rel (Tm Y p c ci) (Tm Y' p c ci) D := by
  intro i k r s
  fin_cases i <;> fin_cases k <;> fin_cases r <;> fin_cases s <;>
    simp [Tm, Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_add, h3]
  all_goals first
    | module
    | linear_combination (norm := module) h1
    | linear_combination (norm := module) h2
    | linear_combination (norm := module) (-1 : K) • h1
    | linear_combination (norm := module) (-1 : K) • h2

end Slots

section General

variable {B : Type} [Ring B]

theorem transp_exch {X T : M2 B} {b : B} (hc : ∀ i j, EC (X i j) T)
    (h : X * T * (Matrix.diagonal fun _ => b) = (Matrix.diagonal fun _ => b) * T * X) :
    Tᵀ * Xᵀ * (Matrix.diagonal fun _ => b) = (Matrix.diagonal fun _ => b) * Xᵀ * Tᵀ := by
  have hc' : ∀ i j, EC (T i j) X := fun i j k l => (hc k l i j).symm
  have h' := congrArg Matrix.transpose h
  rw [transpose_mul_diag, mul_assoc, transpose_diag_mul, transpose_mul_of_comm hc,
    transpose_mul_of_comm hc'] at h'
  rw [h', mul_assoc]

end General

section Slots

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem diagScalar_commute_of_entries {z : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (h : EC z M) : d0 z * M = M * d0 z :=
  diag_comm h

theorem EC_lift0 {z : SlopeTestRemainingChoices S A} {M : M2 A} (h : ∀ i j, Commute z (io (M i j))) : EC z (lift0 M) :=
  fun i j => h i j

theorem rtt_relation_transpose (b : S) (M V : M2 A) (d : K) (h : Rel M V d) :
    lift0 Mᵀ * Rht0 b d * d0 (ins b (lift0 V)) = d0 (ins b (lift0 V)) * Rht0 b d * lift0 Mᵀ := by
  have hc : ∀ i j, EC ((Rh0 b d : M2 (SlopeTestRemainingChoices S A)) i j) (lift0 M) := fun i j k l =>
    (entry_commute_R_matrix (z := io (M k l)) (fun r s => (eU_io b r s _).symm) d i j).symm
  have := transp_exch hc (rtt_relation b M V d h)
  rw [Rh0_transpose] at this
  exact this

theorem Xp_EC {z : SlopeTestRemainingChoices S A} (w : List (Letter K S)) (Y : K)
    (h : ∀ l ∈ w, ∀ i j, Commute z (eU l.intersection_update_fsHerm_neg_one i j)) : EC z (Xp w Y) := by
  induction w with
  | nil => exact EC.one z
  | cons l w ih =>
    have ih' := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    unfold Xp
    split_ifs
    · exact ih'.mul (entry_commute_R_matrix (h l List.mem_cons_self) _)
    · exact ih'

theorem Xm_EC {z : SlopeTestRemainingChoices S A} (w : List (Letter K S)) (Y : K)
    (h : ∀ l ∈ w, ∀ i j, Commute z (eU l.intersection_update_fsHerm_neg_one i j)) : EC z (Xm w Y) := by
  induction w with
  | nil => exact EC.one z
  | cons l w ih =>
    have ih' := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    unfold Xm
    split_ifs
    · exact ih'
    · exact (entry_commute_transposed_R_matrix (h l List.mem_cons_self) _).mul ih'

theorem commute_Avr_Bvr_of_commute_siteOps (σ : Site A) (Y : K) (z : A) (hp : Commute z σ.p) (hc : Commute z σ.c)
    (hci : Commute z σ.ci) (i j : Fin 2) : Commute z (Ts σ Y i j) := by
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm]
  · exact Commute.add_right (Algebra.commute_algebraMap_right Y z) hp
  · exact hc
  · exact hci

end Slots

section Star

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem vlet_free (σ : Site A) (l : Letter K S) {a : S} (h : a ≠ l.intersection_update_fsHerm_neg_one) : FreeOf a (vlet σ l) :=
  ins_free h _ fun _ _ => io_free a _

theorem bT_free (σ : Site A) (w : List (Letter K S)) {a : S} (h : a ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf a (bT σ w) := by
  induction w with
  | nil => exact fun i j => Commute.one_right _
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    exact fun i j => (vlet_free σ l h.1 i j).mul_right (ih h.2 i j)

theorem hol_star {σ : Site A} (hσ : IsSite σ) (Y Y' : K) (i j r s : Fin 2) :
    Commute (Ts σ Y i j) (star (Ts σ Y' r s)) := by
  have hh := hσ.2
  have m1 : σ.p ∈ hol σ := by simp [hol]
  have m2 : σ.c ∈ hol σ := by simp [hol]
  have m3 : σ.ci ∈ hol σ := by simp [hol]
  rw [← commute_star_comm]
  apply commute_Avr_Bvr_of_commute_siteOps <;> rw [commute_star_comm] <;> symm <;> apply commute_Avr_Bvr_of_commute_siteOps
  all_goals first
    | exact (hh _ m1 _ m1).symm
    | exact (hh _ m1 _ m2).symm
    | exact (hh _ m1 _ m3).symm
    | exact (hh _ m2 _ m1).symm
    | exact (hh _ m2 _ m2).symm
    | exact (hh _ m2 _ m3).symm
    | exact (hh _ m3 _ m1).symm
    | exact (hh _ m3 _ m2).symm
    | exact (hh _ m3 _ m3).symm

theorem Ts_star (σ : Site A) {Y : K} (hY : star Y = Y) :
    (Ts σ Y).map star = Tm Y (star σ.p) (star σ.c) (star σ.ci) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm, ← algebraMap_star_comm, hY]

theorem weyl_ci {p c ci : A} (h : WeylRel p c ci) : p * ci = ci * p - ci := by
  obtain ⟨h1, h2, h3⟩ := h
  have : ci * (p * c) * ci = ci * (c * p + c) * ci := by rw [h3]
  have e1 : ci * (p * c) * ci = ci * p := by rw [mul_assoc, mul_assoc, h1, mul_one]
  have e2 : ci * (c * p + c) * ci = p * ci + ci := by
    rw [mul_add, ← mul_assoc, h2, one_mul, add_mul, one_mul]
  rw [e1, e2] at this
  rw [this]; abel

theorem rel_plus {σ : Site A} (hσ : IsSite σ) (Y Ya : K) : Rel (Ts σ Y) (Ts σ Ya) (Y - Ya) := by
  have hw := hσ.1
  refine relT _ _ _ _ _ _ ?_ ?_ ?_
  · rw [hw.2.2]; module
  · rw [weyl_ci hw]; module
  · rw [hw.1, hw.2.1]

theorem rel_minus {σ : Site A} (hσ : IsSite σ) {Y Yb : K} (hY : star Y = Y) (hYb : star Yb = Yb) :
    Rel ((Ts σ Y).map star) ((Ts σ Yb).map star) (Yb - Y) := by
  have hw := hσ.1
  rw [Ts_star σ hY, Ts_star σ hYb]
  refine relT _ _ _ _ _ _ ?_ ?_ ?_
  · have : star σ.c * star σ.p = star σ.p * star σ.c + star σ.c := by
      rw [← star_mul, ← star_mul, ← star_add, hw.2.2]
    rw [this]; module
  · have : star σ.ci * star σ.p = star σ.p * star σ.ci - star σ.ci := by
      rw [← star_mul, ← star_mul, ← star_sub, weyl_ci hw]
    rw [this]; module
  · rw [← star_mul, ← star_mul, hw.1, hw.2.1]

theorem vlet_units (σ : Site A) (l : Letter K S) (w : List (Letter K S))
    (h : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) : ∀ l' ∈ w, ∀ i j, Commute (vlet σ l) (eU l'.intersection_update_fsHerm_neg_one i j) := by
  intro l' hl' i j
  have hne : l'.intersection_update_fsHerm_neg_one ≠ l.intersection_update_fsHerm_neg_one := by
    intro e
    exact h (e ▸ List.mem_map_of_mem hl')
  exact (vlet_free σ l hne i j).symm

theorem Xp_lift0_d0_comm (σ : Site A) (w : List (Letter K S)) (Y : K) (hσ : IsSite σ)
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w) = d0 (bT σ w) * lift0 (Ts σ Y) * Xp w Y := by
  induction w with
  | nil => simp [Xp, bT, d0]
  | cons l w ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    have ih := ih hw.2
    have c1 : d0 (vlet σ l) * Xp w Y = Xp w Y * d0 (vlet σ l) :=
      diagScalar_commute_of_entries (Xp_EC w Y (vlet_units σ l w hw.1))
    by_cases hl : l.plus
    · have c2 : d0 (bT σ w) * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) = Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * d0 (bT σ w) :=
        diagScalar_commute_of_entries (entry_commute_R_matrix (fun i j => (bT_free σ w hw.1 i j).symm) _)
      have s : Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * lift0 (Ts σ Y) * d0 (vlet σ l) =
          d0 (vlet σ l) * lift0 (Ts σ Y) * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) := by
        unfold vlet; rw [if_pos hl]
        exact rtt_relation _ _ _ _ (rel_plus hσ Y l.pt)
      simp only [Xp, bT, if_pos hl, diagScalar_mul]
      calc Xp w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * lift0 (Ts σ Y) * (d0 (vlet σ l) * d0 (bT σ w))
          = Xp w Y * (Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * lift0 (Ts σ Y) * d0 (vlet σ l)) * d0 (bT σ w) := by
            simp only [mul_assoc]
        _ = (Xp w Y * d0 (vlet σ l)) * lift0 (Ts σ Y) * (Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) * d0 (bT σ w)) := by
            rw [s]; simp only [mul_assoc]
        _ = d0 (vlet σ l) * (Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w)) * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) := by
            rw [← c1, ← c2]; simp only [mul_assoc]
        _ = _ := by rw [ih]; simp only [mul_assoc]
    · have c3 : d0 (vlet σ l) * lift0 (Ts σ Y) = lift0 (Ts σ Y) * d0 (vlet σ l) := by
        refine diagScalar_commute_of_entries (EC_lift0 fun i j => ?_)
        unfold vlet; rw [if_neg hl]
        exact (ins_comm _ _ _ (io_free _ _) fun r s => io_comm (hol_star hσ Y l.pt i j r s)).symm
      simp only [Xp, bT, if_neg hl, diagScalar_mul]
      calc Xp w Y * lift0 (Ts σ Y) * (d0 (vlet σ l) * d0 (bT σ w))
          = Xp w Y * (lift0 (Ts σ Y) * d0 (vlet σ l)) * d0 (bT σ w) := by simp only [mul_assoc]
        _ = (Xp w Y * d0 (vlet σ l)) * lift0 (Ts σ Y) * d0 (bT σ w) := by
            rw [← c3]; simp only [mul_assoc]
        _ = d0 (vlet σ l) * (Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w)) := by
            rw [← c1]; simp only [mul_assoc]
        _ = _ := by rw [ih]; simp only [mul_assoc]

end Star

section Star

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem exch2 (σ : Site A) (w : List (Letter K S)) (Y : K) (hσ : IsSite σ)
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : ∀ l ∈ w, star l.pt = l.pt) (hY : star Y = Y) :
    lift0 (Ts σ Y)ᴴ * Xm w Y * d0 (bT σ w) = d0 (bT σ w) * Xm w Y * lift0 (Ts σ Y)ᴴ := by
  induction w with
  | nil => simp [Xm, bT, d0]
  | cons l w ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    have ih := ih hw.2 fun l' hl' => hr l' (List.mem_cons_of_mem _ hl')
    have c1 : d0 (vlet σ l) * Xm w Y = Xm w Y * d0 (vlet σ l) :=
      diagScalar_commute_of_entries (Xm_EC w Y (vlet_units σ l w hw.1))
    by_cases hl : l.plus
    · have c3 : d0 (vlet σ l) * lift0 (Ts σ Y)ᴴ = lift0 (Ts σ Y)ᴴ * d0 (vlet σ l) := by
        refine diagScalar_commute_of_entries (EC_lift0 fun i j => ?_)
        unfold vlet; rw [if_pos hl]
        exact (ins_comm _ _ _ (io_free _ _) fun r s =>
          io_comm (hol_star hσ l.pt Y r s j i).symm).symm
      simp only [Xm, bT, if_pos hl, diagScalar_mul]
      calc lift0 (Ts σ Y)ᴴ * Xm w Y * (d0 (vlet σ l) * d0 (bT σ w))
          = lift0 (Ts σ Y)ᴴ * (Xm w Y * d0 (vlet σ l)) * d0 (bT σ w) := by simp only [mul_assoc]
        _ = (lift0 (Ts σ Y)ᴴ * d0 (vlet σ l)) * Xm w Y * d0 (bT σ w) := by
            rw [← c1]; simp only [mul_assoc]
        _ = d0 (vlet σ l) * (lift0 (Ts σ Y)ᴴ * Xm w Y * d0 (bT σ w)) := by
            rw [← c3]; simp only [mul_assoc]
        _ = _ := by rw [ih]; simp only [mul_assoc]
    · have c2 : d0 (bT σ w) * Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * d0 (bT σ w) :=
        diagScalar_commute_of_entries (entry_commute_transposed_R_matrix (fun i j => (bT_free σ w hw.1 i j).symm) _)
      have s : lift0 (Ts σ Y)ᴴ * Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * d0 (vlet σ l) =
          d0 (vlet σ l) * Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * lift0 (Ts σ Y)ᴴ := by
        unfold vlet; rw [if_neg hl]
        exact rtt_relation_transpose _ _ _ _ (rel_minus hσ hY (hr l List.mem_cons_self))
      simp only [Xm, bT, if_neg hl, diagScalar_mul]
      calc lift0 (Ts σ Y)ᴴ * (Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * Xm w Y) * (d0 (vlet σ l) * d0 (bT σ w))
          = lift0 (Ts σ Y)ᴴ * Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * (Xm w Y * d0 (vlet σ l)) * d0 (bT σ w) := by
            simp only [mul_assoc]
        _ = (lift0 (Ts σ Y)ᴴ * Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * d0 (vlet σ l)) * Xm w Y * d0 (bT σ w) := by
            rw [← c1]; simp only [mul_assoc]
        _ = d0 (vlet σ l) * Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * (lift0 (Ts σ Y)ᴴ * Xm w Y * d0 (bT σ w)) := by
            rw [s]; simp only [mul_assoc]
        _ = d0 (vlet σ l) * (Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * d0 (bT σ w)) * Xm w Y * lift0 (Ts σ Y)ᴴ := by
            rw [ih]; simp only [mul_assoc]
        _ = _ := by rw [← c2]; simp only [mul_assoc]

theorem exch3 (σ : Site A) (w : List (Letter K S)) (Y : K) (hσ : IsSite σ)
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : ∀ l ∈ w, star l.pt = l.pt) (hY : star Y = Y) :
    (Xm w Y)ᵀ * lift0 ((Ts σ Y).map star) * d0 (bT σ w) =
      d0 (bT σ w) * lift0 ((Ts σ Y).map star) * (Xm w Y)ᵀ := by
  have hc : ∀ i j, EC ((lift0 (Ts σ Y)ᴴ : M2 (SlopeTestRemainingChoices S A)) i j) (Xm w Y) := fun i j =>
    Xm_EC w Y fun l _ r s => (eU_io l.intersection_update_fsHerm_neg_one r s _).symm
  exact transp_exch hc (exch2 σ w Y hσ hw hr hY)

theorem exch4 (σ : Site A) (w : List (Letter K S)) (Y : K) (hσ : IsSite σ)
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    lift0 (Ts σ Y)ᵀ * (Xp w Y)ᵀ * d0 (bT σ w) = d0 (bT σ w) * (Xp w Y)ᵀ * lift0 (Ts σ Y)ᵀ := by
  have hc : ∀ i j, EC ((Xp w Y : M2 (SlopeTestRemainingChoices S A)) i j) (lift0 (Ts σ Y)) := fun i j k l =>
    (Xp_EC (z := io (Ts σ Y k l)) w Y (fun l _ r s => (eU_io l.intersection_update_fsHerm_neg_one r s _).symm) i j).symm
  exact transp_exch hc (Xp_lift0_d0_comm σ w Y hσ hw)

end Star

end Formalism.FourierDecayAlt.P.Wd6

namespace Formalism.FourierDecayAlt.P

theorem exchange_plus_factor : Formalism.FourierDecayAlt.Wd.ExchangePlusFactor := by
  intro K A S _ _ _ _ _ _ _ _ σ w Y hσ hw
  exact Wd6.Xp_lift0_d0_comm σ w Y hσ hw.1

theorem exchange_second_case : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorStar := by
  intro K A S _ _ _ _ _ _ _ _ σ w Y hσ hw hY
  exact Wd6.exch2 σ w Y hσ hw.1 hw.2.1 hY

theorem exchange_third_case : Formalism.FourierDecayAlt.Wd.ExchangeMinusFactorTranspose := by
  intro K A S _ _ _ _ _ _ _ _ σ w Y hσ hw hY
  exact Wd6.exch3 σ w Y hσ hw.1 hw.2.1 hY

theorem exchange_fourth_case : Formalism.FourierDecayAlt.Wd.ExchangePlusFactorTranspose := by
  intro K A S _ _ _ _ _ _ _ _ σ w Y hσ hw
  exact Wd6.exch4 σ w Y hσ hw.1

end Formalism.FourierDecayAlt.P
