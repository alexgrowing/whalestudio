import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
open Formalism.REAL Finset Polynomial

namespace GlobalTheory.ScalarNewton

open Matrix

theorem sum_adjugate_eq {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (h : M.det ≠ 0) :
    ∑ a, ∑ b, M.adjugate a b = (M + Matrix.of fun _ _ => (1 : R)).det - M.det := by
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hinj : Function.Injective φ := IsFractionRing.injective R K
  apply hinj
  have hdet : φ M.det = (M.map φ).det := RingHom.map_det φ M
  have hd0 : (M.map φ).det ≠ 0 := by
    rw [← hdet]; exact (map_ne_zero_iff φ hinj).2 h
  have hd : IsUnit (M.map φ).det := hd0.isUnit
  have hJ : (M + Matrix.of fun _ _ => (1 : R)).map φ =
      M.map φ + replicateCol Unit (fun _ : ι => (1 : K)) * replicateRow Unit (fun _ : ι => (1 : K)) := by
    ext i j; simp [replicateCol, replicateRow, Matrix.mul_apply]
  have hadj : ∀ a b, φ (M.adjugate a b) = (M.map φ).adjugate a b := by
    intro a b
    have := congrFun (congrFun (RingHom.map_adjugate φ M) a) b
    simpa using this
  have key := det_add_replicateCol_mul_replicateRow (ι := Unit) hd (fun _ => (1 : K)) (fun _ => 1)
  rw [map_sub, RingHom.map_det φ, RingHom.map_det φ, map_sum]
  simp only [map_sum, hadj]
  change _ = ((M + Matrix.of fun _ _ => (1 : R)).map φ).det - (M.map φ).det
  rw [hJ, key, det_unique (n := Unit), Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply, replicateCol_apply,
    Matrix.smul_apply, smul_eq_mul, one_mul, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hd0]
  ring

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

variable (m : ℕ) (χ : Fin (m + 1) → ℂ)

noncomputable def amat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)

theorem gelfVal_eq (k : ℕ) : GlobalTheory.Dec.gelfVal χ k = ∑ a, ∑ b, (amat m χ ^ k) a b := rfl

noncomputable def pmat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] :=
  (X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + (amat m χ - (m : ℂ) • 1).map C

theorem pmat_apply (a b : Fin (m + 1)) : pmat m χ a b =
    if a = b then X + C (χ a - (m : ℂ) / 2) else if a < b then -1 else 0 := by
  by_cases h1 : a = b
  · subst h1
    simp [pmat, amat, Formalism.REAL.Amat]
    rw [show ((m : ℂ[X])) = C (m : ℂ) from (map_natCast C m).symm, ← C_add, ← C_sub, ← C_sub]
    congr 1
    ring
  · by_cases h2 : a < b
    · simp [pmat, amat, Formalism.REAL.Amat, h1, h2, Matrix.one_apply]
    · simp [pmat, amat, Formalism.REAL.Amat, h1, h2, Matrix.one_apply]

theorem pmat_eq : pmat m χ = (X - C (m : ℂ)) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + (amat m χ).map C := by
  refine Matrix.ext fun a b => ?_
  by_cases h1 : a = b
  · subst h1
    simp [pmat]
    ring
  · simp [pmat, h1, Matrix.one_apply]

theorem det_pmat : (pmat m χ).det = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_congr rfl fun s _ => by rw [pmat_apply]; simp
  · intro i j h
    have h' : j < i := h
    rw [pmat_apply, if_neg (ne_of_gt h'), if_neg (not_lt_of_gt h')]

theorem det_pmat_add : (pmat m χ + Matrix.of fun _ _ => (1 : ℂ[X])).det =
    ∏ s, (X + C (χ s - (m : ℂ) / 2 + 1)) := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_congr rfl fun s _ => by rw [Matrix.add_apply, pmat_apply]; simp; ring
  · intro i j h
    have h' : i < j := h
    rw [Matrix.add_apply, pmat_apply, if_neg (ne_of_lt h'), if_pos h']
    simp

theorem det_pmat_ne_zero : (pmat m χ).det ≠ 0 := by
  rw [det_pmat]
  exact Finset.prod_ne_zero_iff.2 fun s _ => X_add_C_ne_zero _

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

theorem sumEnt_smul {n : ℕ} (c : ℂ[X]) (W : Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (c • W) a b = c * ∑ a, ∑ b, W a b := by
  simp [Finset.mul_sum]

theorem sumEnt_sub {n : ℕ} (V W : Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (V - W) a b = ∑ a, ∑ b, V a b - ∑ a, ∑ b, W a b := by
  simp [Finset.sum_sub_distrib]

theorem sumEnt_sum {n : ℕ} (s : Finset ℕ) (W : ℕ → Matrix (Fin n) (Fin n) ℂ[X]) :
    ∑ a, ∑ b, (∑ i ∈ s, W i : Matrix (Fin n) (Fin n) ℂ[X]) a b = ∑ i ∈ s, ∑ a, ∑ b, W i a b := by
  simp only [Matrix.sum_apply]
  calc _ = ∑ a, ∑ i ∈ s, ∑ b, W i a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem poly_identity (m N : ℕ) (χ : Fin (m + 1) → ℂ) :
    (X - C (m : ℂ)) ^ (N + 1) * ((pmat m χ + Matrix.of fun _ _ => (1 : ℂ[X])).det - (pmat m χ).det) -
      (pmat m χ).det * ∑ k ∈ range (N + 1), (-1) ^ k * (X - C (m : ℂ)) ^ (N - k) * C (GlobalTheory.Dec.gelfVal χ k) =
    (-1) ^ (N + 1) * ∑ a, ∑ b, ((pmat m χ).adjugate * ((amat m χ).map C) ^ (N + 1)) a b := by
  set x : ℂ[X] := X - C (m : ℂ)
  set Bm : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] := (amat m χ).map C
  set Mx := pmat m χ
  have hnp : ∀ i : ℕ, (-Bm) ^ i = ((-1 : ℂ[X]) ^ i) • Bm ^ i := by
    intro i; rw [← neg_one_smul ℂ[X] Bm, _root_.smul_pow]
  have hxp : ∀ i : ℕ, (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) ^ i = x ^ i • 1 := by
    intro i; rw [_root_.smul_pow, one_pow]
  have hBp : ∀ i : ℕ, ∑ a, ∑ b, (Bm ^ i) a b = C (GlobalTheory.Dec.gelfVal χ i) := by
    intro i
    rw [gelfVal_eq, map_sum]
    simp only [map_sum]
    have : Bm ^ i = (amat m χ ^ i).map C := by
      rw [Matrix.map_pow]
    rw [this]
    simp
  have hcomm : Commute (-Bm) (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) :=
    (Commute.one_right _).smul_right x
  have hgeom := hcomm.mul_geom_sum₂ (N + 1)
  set P := ∑ i ∈ range (N + 1), (-Bm) ^ i * (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])) ^ (N + 1 - 1 - i)
  have hMP : Mx * P = x ^ (N + 1) • 1 - (-1 : ℂ[X]) ^ (N + 1) • Bm ^ (N + 1) := by
    have : Mx = -(-Bm - x • 1) := by rw [show Mx = pmat m χ from rfl, pmat_eq]; abel
    rw [this, neg_mul, hgeom, hnp, hxp]
    abel
  have hSP : ∑ a, ∑ b, P a b = ∑ k ∈ range (N + 1), (-1) ^ k * x ^ (N - k) * C (GlobalTheory.Dec.gelfVal χ k) := by
    rw [sumEnt_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnp, hxp, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, sumEnt_smul, hBp]
    simp only [Nat.add_sub_cancel]
  have hadj : Mx.adjugate * Mx = Mx.det • 1 := Matrix.adjugate_mul Mx
  have hdP : Mx.det • P = Mx.adjugate * (Mx * P) := by
    rw [← Matrix.mul_assoc, hadj, Matrix.smul_mul, Matrix.one_mul]
  have hS := congrArg (fun W => ∑ a, ∑ b, W a b) hdP
  rw [sumEnt_smul, hSP, hMP, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, sumEnt_sub,
    sumEnt_smul, sumEnt_smul, sum_adjugate_eq Mx (det_pmat_ne_zero m χ)] at hS
  rw [hS]
  ring

end GlobalTheory.ScalarNewton

namespace GlobalTheory.ScalarNewton

open Matrix

theorem natDegree_adjugate_pmat_le (m : ℕ) (χ : Fin (m + 1) → ℂ) (i j : Fin (m + 1)) :
    ((pmat m χ).adjugate i j).natDegree ≤ m := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  have h1 : ((-1 : ℂ[X]) ^ ((j : ℕ) + i)) = C ((-1) ^ ((j : ℕ) + i)) := by simp
  rw [h1]
  refine (natDegree_C_mul_le _ _).trans ?_
  have e : (pmat m χ).submatrix j.succAbove i.succAbove =
      (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix j.succAbove i.succAbove).map C +
      ((amat m χ - (m : ℂ) • 1).submatrix j.succAbove i.succAbove).map C := rfl
  rw [e]
  simpa using natDegree_det_X_add_C_le
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix j.succAbove i.succAbove)
    ((amat m χ - (m : ℂ) • 1).submatrix j.succAbove i.succAbove)

theorem scalar_newton : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ,
    (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) -
      (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k =
      r.eval u := by
  intro m N χ
  refine ⟨(-1) ^ (N + 1) * ∑ a, ∑ b, ((pmat m χ).adjugate * ((amat m χ).map C) ^ (N + 1)) a b, ?_, ?_⟩
  · have hc : ((-1 : ℂ[X]) ^ (N + 1)) = C ((-1) ^ (N + 1)) := by simp
    rw [hc]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_sum_le_of_forall_le _ _ fun a _ => natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    rw [Matrix.mul_apply]
    refine natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
    rw [← Matrix.map_pow, Matrix.map_apply]
    exact (natDegree_mul_C_le _ _).trans (natDegree_adjugate_pmat_le m χ a c)
  · intro u
    rw [← poly_identity, det_pmat, det_pmat_add]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_prod, eval_add, eval_finset_sum, eval_neg,
      eval_one]
    have e1 : ∏ s, (u + (χ s - (m : ℂ) / 2 + 1)) = ∏ s, (u + 1 - (m : ℂ) / 2 + χ s) :=
      Finset.prod_congr rfl fun _ _ => by ring
    have e0 : ∏ s, (u + (χ s - (m : ℂ) / 2)) = ∏ s, (u - (m : ℂ) / 2 + χ s) :=
      Finset.prod_congr rfl fun _ _ => by ring
    rw [e1, e0]

end GlobalTheory.ScalarNewton
