import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

theorem sum_castLE_eq_sum_ite_lt_formal_degree {M : Type*} [AddCommMonoid M] {n i : ℕ} (hi : i ≤ n) (g : Fin n → M) :
    ∑ a : Fin i, g (Fin.castLE hi a) = ∑ a : Fin n, if (a : ℕ) < i then g a else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hi a) ?_ ?_ ?_ ?_
  · intro a _
    simp [Finset.mem_filter]
  · intro a _ b _ h
    exact Fin.castLE_injective hi h
  · intro b hb
    exact ⟨⟨b, (Finset.mem_filter.1 hb).2⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro a _
    rfl

theorem prod_orderEmbOfFin {R : Type*} [CommMonoid R] {n i : ℕ} (S : Finset (Fin n)) (h : S.card = i)
    (d : Fin n → R) : ∏ k : Fin i, d (S.orderEmbOfFin h k) = ∏ s ∈ S, d s := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S h, Finset.prod_map]
  rfl

theorem leading_minor_conj_diagonal {R : Type*} [CommRing R] (f : ℂ →+* R) {n i : ℕ} (hi : i ≤ n)
    (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → R) :
    ((U.map f * diagonal d * (Uᴴ).map f).submatrix (Fin.castLE hi) (Fin.castLE hi)).det =
      ∑ S : {S : Finset (Fin n) // S.card = i},
        f ((U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).det *
          star (U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).det) * ∏ s ∈ S.1, d s := by
  have hsplit : (U.map f * diagonal d * (Uᴴ).map f).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      ((U.map f).submatrix (Fin.castLE hi) id * diagonal d) * ((Uᴴ).map f).submatrix id (Fin.castLE hi) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
  have hdet : ∀ M : Matrix (Fin i) (Fin i) ℂ, (M.map f).det = f M.det :=
    fun M => (RingHom.map_det f M).symm
  rw [hsplit, cauchyBinet]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hA : ((U.map f).submatrix (Fin.castLE hi) id * diagonal d).submatrix id (S.1.orderEmbOfFin S.2) =
      (U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2)).map f *
        diagonal (fun k => d (S.1.orderEmbOfFin S.2 k)) := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.map_apply]
  have hB : (((Uᴴ).map f).submatrix id (Fin.castLE hi)).submatrix (S.1.orderEmbOfFin S.2) id =
      ((U.submatrix (Fin.castLE hi) (S.1.orderEmbOfFin S.2))ᴴ).map f := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [hA, hB, Matrix.det_mul, Matrix.det_diagonal, hdet, hdet, Matrix.det_conjTranspose,
    prod_orderEmbOfFin S.1 S.2 d, map_mul]
  ring

open Polynomial in
theorem coeff_prod_one_add_low {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℂ) :
    (∏ s ∈ S, (1 + X * C (v s))).coeff 0 = 1 ∧ (∏ s ∈ S, (1 + X * C (v s))).coeff 1 = ∑ s ∈ S, v s ∧
    2 * (∏ s ∈ S, (1 + X * C (v s))).coeff 2 = (∑ s ∈ S, v s) ^ 2 - ∑ s ∈ S, v s ^ 2 := by
  refine Finset.induction_on S ?_ ?_
  · simp [Polynomial.coeff_one]
  · intro a S ha ih
    obtain ⟨h0, h1, h2⟩ := ih
    have e : ∀ P : ℂ[X], (1 + X * C (v a)) * P = P + X * (C (v a) * P) := fun P => by ring
    rw [Finset.prod_insert ha, e, Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, h0, add_zero]
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, h1, h0]
      ring
    · rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, mul_add, h2, h1]
      ring

open Polynomial in
theorem conj_polynomial_diagonal {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (hV : V * Vᴴ = 1) (ν : Fin m → ℂ) :
    V.map C * diagonal (fun s => 1 + X * C (ν s)) * (Vᴴ).map C =
      1 + (X : ℂ[X]) • (V * diagonal ν * Vᴴ).map C := by
  have hD : diagonal (fun s => 1 + X * C (ν s)) = 1 + (X : ℂ[X]) • (diagonal ν).map C := by
    ext a b
    by_cases h : a = b
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hV,
    Matrix.map_one _ (map_zero C) (map_one C)]

theorem trace_conj_eq_trace_of_conjTranspose_mul_self {m : ℕ} (V D : Matrix (Fin m) (Fin m) ℂ) (hV : Vᴴ * V = 1) :
    trace (V * D * Vᴴ) = trace D := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

theorem sq_conj_diagonal {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (ν : Fin m → ℂ) (hV : Vᴴ * V = 1) :
    V * diagonal ν * Vᴴ * (V * diagonal ν * Vᴴ) = V * diagonal (fun s => ν s ^ 2) * Vᴴ := by
  calc V * diagonal ν * Vᴴ * (V * diagonal ν * Vᴴ) = V * diagonal ν * (Vᴴ * V) * diagonal ν * Vᴴ := by
        simp only [Matrix.mul_assoc]
    _ = V * diagonal (fun s => ν s ^ 2) * Vᴴ := by
        rw [hV, Matrix.mul_one, Matrix.mul_assoc V, Matrix.diagonal_mul_diagonal]
        simp [sq]

open Polynomial in
theorem coeff_two_det_hermitian {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.IsHermitian) :
    2 * (det (1 + (X : ℂ[X]) • A.map C)).coeff 2 = (trace A) ^ 2 - trace (A * A) := by
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  set ν : Fin m → ℂ := fun s => ((hA.eigenvalues s : ℝ) : ℂ) with hν
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.prop
  have hUU' : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.prop
  have hAeq : A = U * diagonal ν * Uᴴ := hA.spectral_theorem
  have hconj := conj_polynomial_diagonal U hUU ν
  have hdU : (U.map C).det * ((Uᴴ).map C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero C) (map_one C), Matrix.det_one]
  have hdet : (1 + (X : ℂ[X]) • (U * diagonal ν * Uᴴ).map C).det = ∏ s, (1 + X * C (ν s)) := by
    rw [← hconj, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm ((U.map C).det), mul_assoc,
      hdU, mul_one]
  rw [hAeq, hdet, (coeff_prod_one_add_low Finset.univ ν).2.2, sq_conj_diagonal U ν hUU', trace_conj_eq_trace_of_conjTranspose_mul_self U _ hUU',
    trace_conj_eq_trace_of_conjTranspose_mul_self U _ hUU', Matrix.trace_diagonal, Matrix.trace_diagonal]

theorem trace_leading_submatrix {n i : ℕ} (hi : i ≤ n) (M : Matrix (Fin n) (Fin n) ℂ) :
    trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi)) = ∑ a : Fin n, if (a : ℕ) < i then M a a else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact sum_castLE_eq_sum_ite_lt_formal_degree hi (fun a => M a a)

theorem variance_eq_trace_diff {n i : ℕ} (hi : i ≤ n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian) :
    ((Vi M i : ℝ) : ℂ) = trace ((M * M).submatrix (Fin.castLE hi) (Fin.castLE hi)) -
      trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi)) := by
  have hMab : ∀ a b, M a b * M b a = (‖M b a‖ : ℂ) ^ 2 := by
    intro a b
    rw [← hM.apply a b]
    exact Complex.conj_mul' (M b a)
  have h1 : trace ((M * M).submatrix (Fin.castLE hi) (Fin.castLE hi)) =
      ∑ a : Fin n, if (a : ℕ) < i then ∑ b : Fin n, M a b * M b a else 0 := by
    rw [trace_leading_submatrix hi]
    simp only [Matrix.mul_apply]
  have inner : ∀ a : Fin n, ∑ b : Fin i, M a (Fin.castLE hi b) * M (Fin.castLE hi b) a =
      ∑ b : Fin n, if (b : ℕ) < i then M a b * M b a else 0 :=
    fun a => sum_castLE_eq_sum_ite_lt_formal_degree hi (fun b => M a b * M b a)
  have h2 : trace (M.submatrix (Fin.castLE hi) (Fin.castLE hi) * M.submatrix (Fin.castLE hi) (Fin.castLE hi)) =
      ∑ a : Fin n, if (a : ℕ) < i then
        ∑ b : Fin n, (if (b : ℕ) < i then M a b * M b a else 0) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.submatrix_apply]
    calc ∑ a : Fin i, ∑ b : Fin i, M (Fin.castLE hi a) (Fin.castLE hi b) * M (Fin.castLE hi b) (Fin.castLE hi a)
        = ∑ a : Fin i, (fun a' : Fin n => ∑ b : Fin n, if (b : ℕ) < i then M a' b * M b a' else 0)
            (Fin.castLE hi a) := Finset.sum_congr rfl fun a _ => inner _
      _ = _ := sum_castLE_eq_sum_ite_lt_formal_degree hi (fun a' : Fin n => ∑ b : Fin n, if (b : ℕ) < i then M a' b * M b a' else 0)
  rw [h1, h2, ← Finset.sum_sub_distrib]
  simp only [Vi, Complex.ofReal_sum, apply_ite Complex.ofReal, Complex.ofReal_zero, Complex.ofReal_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < i
  · rw [if_pos ha, if_pos ha, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : (b : ℕ) < i
    · rw [if_pos hb, sub_self, if_neg (by omega)]
    · rw [if_neg hb, sub_zero, if_pos (by omega), hMab]
  · rw [if_neg ha, if_neg ha, sub_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (by omega)]

end ReciprocityTheory.ChartRestriction.DS
