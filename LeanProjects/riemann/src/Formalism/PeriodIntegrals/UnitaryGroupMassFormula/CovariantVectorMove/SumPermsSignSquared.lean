import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantVectorMove.MoveOperatorCovariance

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmMove

theorem rho_sum {A : Type*} [Ring A] (m : ℕ) (z : ℤ) (x D : A) :
    ∑ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      (x * (((Equiv.Perm.sign ρ : ℤ) : A) * D)) = (m.factorial : A) * ((z : A) * (x * D)) := by
  have h : ∀ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      (x * (((Equiv.Perm.sign ρ : ℤ) : A) * D)) = (z : A) * (x * D) := by
    intro ρ
    rw [sgnlem, ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A), ← Int.cast_mul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => h ρ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

theorem sum_perms_sign_squared {A : Type*} [Ring A] (m : ℕ) (z : ℤ) (x D : A) :
    ∑ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      ((((Equiv.Perm.sign ρ : ℤ) : A) * D) * x) = (m.factorial : A) * ((z : A) * (D * x)) := by
  have h : ∀ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      ((((Equiv.Perm.sign ρ : ℤ) : A) * D) * x) = (z : A) * (D * x) := by
    intro ρ
    rw [Int.cast_mul, mul_assoc, ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A) _ x,
      ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A) ((Equiv.Perm.sign ρ : ℤ) : A) D, ← Int.cast_mul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => h ρ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

section Vec
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
  (a : Fin m → Fin n) (b : Fin (m + 1) → Fin n) (w : ℂ)

def Fv (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) (σ : Equiv.Perm (Fin m)) (q : Fin (m + 1)) : A :=
  if (q : ℕ) = p then y (b (τ q))
  else if (q : ℕ) < p then Tm E (w - 1 - ((q : ℕ) : ℂ)) (extN (a ∘ σ) (b 0) q) (b (τ q))
  else Tm E (w - (((q : ℕ) - 1 : ℕ) : ℂ)) (extN (a ∘ σ) (b 0) ((q : ℕ) - 1)) (b (τ q))

def Pv (p : ℕ) (τ : Equiv.Perm (Fin (m + 1))) : A :=
  ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn (Fv E y a b w p τ σ)).prod

def Mv (p : ℕ) : A := ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * Pv E y a b w p τ

omit [Algebra ℂ A] in

def symV (x c d : Fin n) : A := (if x = d then y c else 0) + (if x = c then y d else 0)

omit [Algebra ℂ A] in
theorem symV_comm (x c d : Fin n) : symV y x c d = symV y x d c := by
  simp only [symV]; abel

theorem midV (hy : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (v v' : ℂ) (hv : v = v' + 1) (x d c : Fin n) :
    y c * Tm E v x d - Tm E v' x d * y c = symV y x c d := by
  have h := hy x d c
  rw [sub_eq_iff_eq_add] at h
  have c2 : ∀ z, algebraMap ℂ A v' * y z = y z * algebraMap ℂ A v' := fun z => Algebra.commutes _ _
  subst hv
  simp only [Tm, symV]
  split_ifs at h ⊢
  all_goals
    simp only [map_add, map_one, mul_add, add_mul, mul_one, zero_add, add_zero, h, c2]
    try noncomm_ring

theorem stepV (hy : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (p : ℕ) (hp : p < m) : Mv E y a b w (p + 1) = -Mv E y a b w p := by
  set s : Equiv.Perm (Fin (m + 1)) := Equiv.swap ⟨p, by omega⟩ ⟨p + 1, by omega⟩ with hs_def
  have hs : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  have hfix : ∀ q : Fin (m + 1), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 → s q = q := by
    intro q h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]
    · intro h; apply h2; rw [h]
  have hoff : ∀ τ σ (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fv E y a b w p (τ * s) σ q = Fv E y a b w p τ σ q := by
    intro τ σ q h1 h2
    simp only [Fv, Equiv.Perm.mul_apply, hfix q h1 h2]
  have hoff2 : ∀ τ σ (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fv E y a b w (p + 1) τ σ q = Fv E y a b w p τ σ q := by
    intro τ σ q h1 h2
    have e1 : ((q : ℕ) < p + 1) ↔ ((q : ℕ) < p) := by omega
    simp only [Fv, if_neg h1, if_neg h2, e1]
  have htk : ∀ τ σ, (List.ofFn (Fv E y a b w p (τ * s) σ)).take p =
      (List.ofFn (Fv E y a b w p τ σ)).take p :=
    fun τ σ => take_ofFn_congr _ _ p (fun k hk => hoff τ σ k (by omega) (by omega))
  have hdr : ∀ τ σ, (List.ofFn (Fv E y a b w p (τ * s) σ)).drop (p + 2) =
      (List.ofFn (Fv E y a b w p τ σ)).drop (p + 2) :=
    fun τ σ => drop_ofFn_congr _ _ (p + 2) (fun k hk => hoff τ σ k (by omega) (by omega))
  have hsp : s ⟨p, by omega⟩ = ⟨p + 1, by omega⟩ := Equiv.swap_apply_left _ _
  have hsp1 : s ⟨p + 1, by omega⟩ = ⟨p, by omega⟩ := Equiv.swap_apply_right _ _
  have n1 : p + 1 ≠ p := by omega
  have n2 : p < p + 1 := by omega
  have n3 : ¬ (p + 1 < p) := by omega
  have n4 : p + 1 - 1 = p := by omega
  refine step s hs (fun τ => Pv E y a b w p τ) (fun τ => Pv E y a b w (p + 1) τ)
    (fun τ => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : A) *
      (((List.ofFn (Fv E y a b w p τ σ)).take p).prod *
        symV y (extN (a ∘ σ) (b 0) p) (b (τ ⟨p + 1, by omega⟩)) (b (τ ⟨p, by omega⟩)) *
        ((List.ofFn (Fv E y a b w p τ σ)).drop (p + 2)).prod)) ?_ ?_
  · intro τ
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [htk, hdr, Equiv.Perm.mul_apply, hsp, hsp1]
    rw [symV_comm]
  · intro τ
    simp only [Pv]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← mul_sub, prod_diff _ _ p (by omega)
      (fun k h1 h2 => (hoff2 τ σ k h1 h2).trans (hoff τ σ k h1 h2).symm), htk, hdr]
    congr 1
    congr 2
    simp only [Fv, Equiv.Perm.mul_apply, hsp, hsp1, if_true, if_neg n1, if_pos n2, if_neg n3, n4,
      if_neg n1.symm]
    exact midV E y hy _ _ (by push_cast; ring) _ _ _

theorem Pv_zero (τ : Equiv.Perm (Fin (m + 1))) :
    Pv E y a b w 0 τ = y (b (τ 0)) * qminor E a (fun k => b (τ k.succ)) w := by
  unfold Pv qminor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [List.ofFn_succ, List.prod_cons]
  have hf : Fv E y a b w 0 τ σ 0 = y (b (τ 0)) := by simp [Fv]
  have hg : (fun i : Fin m => Fv E y a b w 0 τ σ i.succ) =
      fun k : Fin m => Tm E (w - (k : ℂ)) (a (σ k)) (b (τ k.succ)) := by
    funext k
    simp only [Fv, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, extN_lt] <;> rfl
  rw [hf, hg, ← mul_assoc, ← mul_assoc, icomm]

theorem Pv_last (τ : Equiv.Perm (Fin (m + 1))) :
    Pv E y a b w m τ = qminor E a (fun k => b (τ k.castSucc)) (w - 1) * y (b (τ (Fin.last m))) := by
  unfold Pv qminor
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  have hf : Fv E y a b w m τ σ (Fin.last m) = y (b (τ (Fin.last m))) := by simp [Fv]
  have hg : (fun i : Fin m => Fv E y a b w m τ σ i.castSucc) =
      fun k : Fin m => Tm E (w - 1 - (k : ℂ)) (a (σ k)) (b (τ k.castSucc)) := by
    funext k
    simp only [Fv, Fin.val_castSucc]
    rw [if_neg (by have := k.isLt; omega), if_pos k.isLt, extN_lt] <;> rfl
  rw [hf, hg]
  exact (mul_assoc _ _ _).symm

theorem Mv_zero (hE : GlRel E) : Mv E y a b w 0 = (m.factorial : A) * ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) := by
  unfold Mv
  rw [sum_perm_eq_sum_firstColumnSplit m, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hP : ∀ ρ, Pv E y a b w 0 (phi0 m (j, ρ)) =
      y (b j) * (((Equiv.Perm.sign ρ : ℤ) : A) * qminor E a (b ∘ j.succAbove) w) := by
    intro ρ
    rw [Pv_zero, firstColumnSplit_zero, ← quantumMinorColSkew_holds A n m E hE a (b ∘ j.succAbove) ρ w]
    congr 2
    funext k
    simp [firstColumnSplit_succ]
  simp only [hP, sign_firstColumnSplit, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  exact rho_sum m _ _ _

theorem Mv_last (hE : GlRel E) : Mv E y a b w m = (m.factorial : A) * ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) * (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j)) := by
  unfold Mv
  rw [sum_phiL m, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hP : ∀ ρ, Pv E y a b w m (lastColumnSplit m (j, ρ)) =
      (((Equiv.Perm.sign ρ : ℤ) : A) * qminor E a (b ∘ j.succAbove) (w - 1)) * y (b j) := by
    intro ρ
    rw [Pv_last, phiL_last, ← quantumMinorColSkew_holds A n m E hE a (b ∘ j.succAbove) ρ (w - 1)]
    congr 2
    funext k
    simp [phiL_castSucc]
  simp only [hP, phiL_sign, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  exact sum_perms_sign_squared m _ _ _

end Vec

theorem move_operator_vector : PI.MoveVec := by
  intro A _ _ n t E y hE hy _ a b w
  have hc := chain (Mv E y a b w) t (fun p hp => stepV E y a b w hy p hp)
  rw [Mv_last E y a b w hE, Mv_zero E y a b w hE] at hc
  have hs : ∀ X : Fin (t + 1) → A, ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (t - (j : ℕ)) : ℤ) : A) * X j =
      (((-1 : ℤ) ^ t : ℤ) : A) * ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * X j := by
    intro X
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [neg_one_pow_sub t j (Nat.lt_succ_iff.mp j.isLt), Int.cast_mul, mul_assoc]
  rw [hs, ← mul_assoc (((-1 : ℤ) ^ t : ℤ) : A), icomm ((-1 : ℤ) ^ t) (t.factorial : A), mul_assoc] at hc
  have h2 := fact_cancel t _ _ hc
  have hsq : (((-1 : ℤ) ^ t : ℤ) : A) * (((-1 : ℤ) ^ t : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, Int.cast_one]
  calc _ = ((((-1 : ℤ) ^ t : ℤ) : A) * (((-1 : ℤ) ^ t : ℤ) : A)) * ∑ j : Fin (t + 1),
        (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) := by
        rw [hsq, one_mul]
    _ = _ := by rw [mul_assoc, ← h2, ← mul_assoc, hsq, one_mul]

end PI.UnitaryGroupMassFormula.QmMove
