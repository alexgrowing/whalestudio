import ReciprocityTheory.DualLattices.UpSmith

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.Smith

section general

variable {R : Type} [CommRing R]

def Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun k l =>
    if l = j0 then (if k = j0 then 1 else 0) else ((if k = l then 1 else 0) - (if k = j0 then s l else 0))

theorem det_Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : (Vm j0 s).det = 1 := by
  rw [Matrix.det_succ_column (Vm j0 s) j0, Finset.sum_eq_single j0]
  · have hsub : (Vm j0 s).submatrix j0.succAbove j0.succAbove = 1 := by
      ext k l
      simp only [Matrix.submatrix_apply, Vm, Matrix.of_apply, Fin.succAbove_ne, if_false,
        sub_zero, Matrix.one_apply, (Fin.succAbove_right_injective).eq_iff]
    rw [hsub, Matrix.det_one]
    simp [Vm, ← two_mul, pow_mul]
  · intro k _ hk
    simp [Vm, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_Vm {m N : ℕ} (X : Matrix (Fin m) (Fin (N + 1)) R) (j0 : Fin (N + 1))
    (s : Fin (N + 1) → R) (i : Fin m) (l : Fin (N + 1)) :
    (X * Vm j0 s) i l = if l = j0 then X i j0 else X i l - s l * X i j0 := by
  classical
  simp only [Matrix.mul_apply, Vm, Matrix.of_apply]
  by_cases hl : l = j0
  · simp [hl]
  · simp only [hl, if_false, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem VmT_mul {N n : ℕ} (j0 : Fin (N + 1)) (u : Fin (N + 1) → R) (Y : Matrix (Fin (N + 1)) (Fin n) R)
    (k : Fin (N + 1)) (l : Fin n) :
    ((Vm j0 u)ᵀ * Y) k l = if k = j0 then Y j0 l else Y k l - u k * Y j0 l := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Vm, Matrix.of_apply]
  by_cases hk : k = j0
  · simp [hk]
  · simp only [hk, if_false, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq']

def piv {N : ℕ} (i0 : Fin (N + 1)) : Equiv.Perm (Fin (N + 1)) :=
  (finSuccEquiv N).trans (finSuccEquiv' i0).symm

theorem piv_zero {N : ℕ} (i0 : Fin (N + 1)) : piv i0 0 = i0 := by
  simp [piv, finSuccEquiv_zero]

theorem piv_succ {N : ℕ} (i0 : Fin (N + 1)) (l : Fin N) : piv i0 l.succ = i0.succAbove l := by
  simp [piv, finSuccEquiv_succ]

def bd1 {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : Matrix (Fin (N + 1)) (Fin (M + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun l => Fin.cases 0 (fun k => P l k) j) i

@[simp] theorem blockOne_zero_zero_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : bd1 P 0 0 = 1 := rfl
@[simp] theorem blockOne_zero_succ_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (k : Fin M) :
    bd1 P 0 k.succ = 0 := rfl
@[simp] theorem blockOne_succ_zero_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (l : Fin N) :
    bd1 P l.succ 0 = 0 := rfl
@[simp] theorem blockOne_succ_succ_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (l : Fin N) (k : Fin M) :
    bd1 P l.succ k.succ = P l k := rfl

theorem det_blockOne_alt {N : ℕ} (P : Matrix (Fin N) (Fin N) R) : (bd1 P).det = P.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [blockOne_zero_zero_alt, blockOne_zero_succ_alt, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one,
    Fin.val_zero, pow_zero, one_mul]
  all_goals congr 1

theorem blockOne_mul_mul_blockOne {d n : ℕ} (P : Matrix (Fin d) (Fin d) R) (Cm : Matrix (Fin (d + 1)) (Fin (n + 1)) R)
    (Q : Matrix (Fin n) (Fin n) R) (h0 : ∀ k : Fin n, Cm 0 k.succ = 0)
    (h1 : ∀ l : Fin d, Cm l.succ 0 = 0) :
    (bd1 P * Cm * bd1 Q) 0 0 = Cm 0 0 ∧ (∀ k : Fin n, (bd1 P * Cm * bd1 Q) 0 k.succ = 0) ∧
      (∀ l : Fin d, (bd1 P * Cm * bd1 Q) l.succ 0 = 0) ∧
      ∀ (l : Fin d) (k : Fin n), (bd1 P * Cm * bd1 Q) l.succ k.succ =
        (P * (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) * Q) l k := by
  have hPC0 : ∀ j : Fin (n + 1), (bd1 P * Cm) 0 j = Cm 0 j := by
    intro j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have hPCs : ∀ (l : Fin d) (j : Fin (n + 1)), (bd1 P * Cm) l.succ j = ∑ m, P l m * Cm m.succ j := by
    intro l j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨?_, fun k => ?_, fun l => ?_, fun l k => ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [hPCs, h1]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [hPCs, blockOne_zero_succ_alt, mul_zero, zero_add, blockOne_succ_succ_alt, Matrix.mul_apply, Matrix.of_apply]

theorem isUnit_det_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) R).det := by
  have h := Matrix.det_permutation (R := R) σ
  simp only [Equiv.Perm.permMatrix] at h
  rw [h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end general

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem smith_mat (hv : v.Integers R) : ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) R),
    ∃ (P : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin n) (Fin n) R) (a : Fin d → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ ∀ j k, (P * A * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0
  | 0, n, A => ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
  | d + 1, 0, A => ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
  | d + 1, n + 1, A => by
    classical
    set g : Fin (n + 1) → Fin (d + 1) → R := fun j i => A i j with hg
    obtain ⟨i0, a, u, s, hu, hau, hs, hz, hnz⟩ := exists_pivot hv g
    by_cases ha : a = 0
    · have hA : A = 0 := by
        ext i j
        have := congrFun (hz ha j) i
        simpa [hg] using this
      exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hA]⟩
    · obtain ⟨j0, hj0, hs0⟩ := hnz ha
      have hAj0 : ∀ i, A i j0 = a * u i := fun i => by
        have := congrFun hj0 i
        simpa [hg] using this
      have hAi0 : ∀ l, A i0 l = a * s l := fun l => by
        have := hs l
        simpa [hg] using this
      set B := (Vm i0 u)ᵀ * A * Vm j0 s with hBdef
      have hB : ∀ k l, B k l = if k = i0 then (if l = j0 then a else 0) else
          (if l = j0 then 0 else A k l - s l * (a * u k)) := by
        intro k l
        rw [hBdef, Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
        by_cases hk : k = i0 <;> by_cases hl : l = j0
        · subst hk; subst hl; simp [hAj0, hu]
        · subst hk; simp [hl, hAi0, hs0]; ring
        · subst hl; simp [hk, hAj0, hu, hs0]; ring
        · simp [hk, hl, hAj0, hAi0, hu]; ring
      set A'' : Matrix (Fin d) (Fin n) R := Matrix.of fun l k => B (i0.succAbove l) (j0.succAbove k)
      obtain ⟨P'', Q'', a'', hP'', hQ'', hD''⟩ := smith_mat hv d n A''
      set Cm := B.submatrix (piv i0) (piv j0) with hCm
      have hCeq : ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * B * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Cm := by
        rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
        rfl
      have h0 : ∀ k : Fin n, Cm 0 k.succ = 0 := by
        intro k
        simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, if_true,
          Fin.succAbove_ne, if_false]
      have h1 : ∀ l : Fin d, Cm l.succ 0 = 0 := by
        intro l
        simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, Fin.succAbove_ne, if_false,
          if_true]
      have hsub : (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) = A'' := by
        ext l k
        simp only [hCm, Matrix.of_apply, Matrix.submatrix_apply, piv_succ]
        rfl
      obtain ⟨e00, e0s, es0, ess⟩ := blockOne_mul_mul_blockOne P'' Cm Q'' h0 h1
      refine ⟨bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ,
        Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'', Fin.cons a a'', ?_, ?_, ?_⟩
      · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
        exact hP''.mul (isUnit_det_perm _)
      · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
        exact (isUnit_det_perm _).mul hQ''
      · have hfull : bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ * A *
            (Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'') = bd1 P'' * Cm * bd1 Q'' := by
          rw [← hCeq, hBdef]
          simp only [Matrix.mul_assoc]
        intro j k
        rw [hfull]
        refine Fin.cases ?_ (fun l => ?_) j <;> refine Fin.cases ?_ (fun k' => ?_) k
        · rw [e00]
          simp [hCm, piv_zero, hB]
        · rw [e0s]
          simp
        · rw [es0]
          simp
        · rw [ess, hsub, hD'']
          simp [Fin.val_succ]

end ReciprocityTheory.PGsh.Up.Smith
