import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.GGEq

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem sum_rows {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommGroup M]
    [Module ℂ M] (p : Fin (m + 2) → α → ℂ) (f g : α → ℂ) (Φ : (Fin m → α) → M) :
    ∑ x : Fin (m + 2) → α, (f (x 0) * g (x 1) * ∏ k, p k (x k)) • Φ (fun k => x k.succ.succ) =
      ((∑ z, f z * p 0 z) * (∑ z, g z * p 1 z)) •
        ∑ y : Fin m → α, (∏ k, p k.succ.succ (y k)) • Φ y := by
  rw [sum_fun_succ]
  simp_rw [sum_fun_succ (r := m)]
  simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.prod_univ_succ, Fin.succ_zero_eq_one]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_smul, Finset.smul_sum, smul_smul]
  symm
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun x1 _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun y _ => ?_
  congr 1
  ring

theorem sum_sgnL_prod_row {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → Fin N) :
    ∑ c : Fin N → Fin N, sgnL c id * ∏ k, P (x k) (c k) = sgnL x id * P.det := by
  have h1 := sum_sgnL (M := ℂ) (id : Fin N → Fin N) (fun c => ∏ k, P (x k) (c k))
  simp only [smul_eq_mul] at h1
  rw [h1]
  have h2 : (Matrix.of fun i k => P (x k) i).det = sgnL x id * P.det := by
    have h3 : (Matrix.of fun i k => P (x k) i) =
        ((Matrix.of fun k j => if x k = id j then (1 : ℂ) else 0) * P).transpose := by
      ext i k
      simp [Matrix.mul_apply]
    rw [h3, Matrix.det_transpose, Matrix.det_mul]
    rfl
  rw [← h2, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

theorem sum_sgnL_prod_col {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → Fin N) :
    ∑ d : Fin N → Fin N, sgnL d id * ∏ k, Q (d k) (y k) = sgnL y id * Q.det := by
  have h1 := sum_sgnL (M := ℂ) (id : Fin N → Fin N) (fun d => ∏ k, Q (d k) (y k))
  simp only [smul_eq_mul] at h1
  rw [h1]
  have h2 : (Matrix.of fun i k => Q i (y k)).det = sgnL y id * Q.det := by
    have h3 : (Matrix.of fun i k => Q i (y k)) =
        Q * (Matrix.of fun k j => if y k = id j then (1 : ℂ) else 0).transpose := by
      ext i k
      simp [Matrix.mul_apply]
    rw [h3, Matrix.det_mul, Matrix.det_transpose, mul_comm]
    rfl
  rw [← h2, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

theorem sum_swap4 {ι κ : Type*} [Fintype ι] [Fintype κ] {M : Type*} [AddCommMonoid M]
    (f : ι → ι → κ → κ → M) :
    ∑ c, ∑ d, ∑ x, ∑ y, f c d x y = ∑ x, ∑ y, ∑ c, ∑ d, f c d x y := by
  calc ∑ c, ∑ d, ∑ x, ∑ y, f c d x y = ∑ c, ∑ x, ∑ d, ∑ y, f c d x y :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
    _ = ∑ x, ∑ c, ∑ d, ∑ y, f c d x y := Finset.sum_comm
    _ = ∑ x, ∑ c, ∑ y, ∑ d, f c d x y :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
    _ = ∑ x, ∑ y, ∑ c, ∑ d, f c d x y := Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

theorem GG_cov {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F F' : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (P Q : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
    (hLin : ∀ x y : Fin m → Fin (m + 2), F' x y =
      ∑ c : Fin m → Fin (m + 2), ∑ d : Fin m → Fin (m + 2),
        ((∏ k, P (c k) (x k)) * ∏ k, Q (y k) (d k)) • F c d)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F' (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a') = (P.det * Q.det) • GG F β β' a a' := by
  have hv : ∀ (v : Fin (m + 2) → ℂ) (i : Fin (m + 2)), (v ᵥ* P) i = ∑ z, v z * P z i := by
    intro v i
    simp [Matrix.vecMul, dotProduct]
  have hw : ∀ (v : Fin (m + 2) → ℂ) (i : Fin (m + 2)), (Q *ᵥ v) i = ∑ z, v z * Q i z := by
    intro v i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have key : ∀ c d : Fin (m + 2) → Fin (m + 2),
      (sgnL c id * sgnL d id * ((β ᵥ* P) (c 0) * (β' ᵥ* P) (c 1)) *
          ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1))) •
        F' (fun k => c k.succ.succ) (fun k => d k.succ.succ) =
      ∑ x : Fin (m + 2) → Fin (m + 2), ∑ y : Fin (m + 2) → Fin (m + 2),
        (sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1)))) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ) := by
    intro c d
    have e1 : ∀ x : Fin (m + 2) → Fin (m + 2),
        ∑ y : Fin (m + 2) → Fin (m + 2), (a (y 0) * a' (y 1) * ∏ k, Q (d k) (y k)) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ) =
          ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F (fun k => x k.succ.succ) y := by
      intro x
      rw [sum_rows (fun k z => Q (d k) z) a a' (fun y => F (fun k => x k.succ.succ) y), hw a, hw a']
    have e2 : ∑ x : Fin (m + 2) → Fin (m + 2), (β (x 0) * β' (x 1) * ∏ k, P (x k) (c k)) •
          (((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F (fun k => x k.succ.succ) y) =
        ((β ᵥ* P) (c 0) * (β' ᵥ* P) (c 1)) • ∑ x : Fin m → Fin (m + 2), (∏ k, P (x k) (c k.succ.succ)) •
          (((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F x y) := by
      rw [sum_rows (fun k z => P z (c k)) β β' (fun x => ((Q *ᵥ a) (d 0) * (Q *ᵥ a') (d 1)) •
            ∑ y : Fin m → Fin (m + 2), (∏ k, Q (d k.succ.succ) (y k)) • F x y), hv β, hv β']
    have e3 : (∑ x : Fin (m + 2) → Fin (m + 2), ∑ y : Fin (m + 2) → Fin (m + 2),
        (sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1)))) •
            F (fun k => x k.succ.succ) (fun k => y k.succ.succ)) =
        (sgnL c id * sgnL d id) • ∑ x : Fin (m + 2) → Fin (m + 2),
          (β (x 0) * β' (x 1) * ∏ k, P (x k) (c k)) • ∑ y : Fin (m + 2) → Fin (m + 2),
            (a (y 0) * a' (y 1) * ∏ k, Q (d k) (y k)) •
              F (fun k => x k.succ.succ) (fun k => y k.succ.succ) := by
      simp only [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      congr 1
      ring
    rw [e3]
    simp_rw [e1]
    rw [e2, hLin]
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring
  unfold GG
  simp_rw [key]
  rw [sum_swap4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [← Finset.sum_smul, smul_smul]
  congr 1
  have hcd : ∑ c : Fin (m + 2) → Fin (m + 2), ∑ d : Fin (m + 2) → Fin (m + 2),
      sgnL c id * (∏ k, P (x k) (c k)) * (sgnL d id * ∏ k, Q (d k) (y k)) *
        (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1))) =
      (∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id * ∏ k, P (x k) (c k)) *
        (∑ d : Fin (m + 2) → Fin (m + 2), sgnL d id * ∏ k, Q (d k) (y k)) *
          (β (x 0) * β' (x 1) * (a (y 0) * a' (y 1))) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
  rw [hcd, sum_sgnL_prod_row, sum_sgnL_prod_col]
  ring

end PI.QnCovHat2W
