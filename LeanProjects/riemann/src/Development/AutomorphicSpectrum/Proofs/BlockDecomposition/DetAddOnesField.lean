import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AdjSum

open Matrix Polynomial

theorem det_add_ones_field {K : Type*} [Field K] {n : ℕ} (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) :
    (B + Matrix.of fun _ _ => (1 : K)).det = B.det + ∑ a, ∑ b, B.adjugate a b := by
  have hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin n) (Fin n) K) =
      replicateCol Unit (fun _ => (1 : K)) * replicateRow Unit (fun _ => (1 : K)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hJ, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hB)]
  have hinv : B⁻¹ = (B.det)⁻¹ • B.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have h1 : ∀ C : Matrix Unit Unit K, C.det = C () () := fun C => det_unique C
  rw [h1, hinv]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.smul_apply,
    replicateRow_apply, replicateCol_apply, one_mul, mul_one, smul_eq_mul, Finset.univ_unique,
    Finset.sum_singleton]
  rw [mul_add, mul_one]
  congr 1
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  field_simp

theorem det_add_ones {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) :
    (A + Matrix.of fun _ _ => (1 : R)).det = A.det + ∑ a, ∑ b, A.adjugate a b := by
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have hdet : ∀ C : Matrix (Fin n) (Fin n) R, f C.det = (C.map f).det := fun C =>
    RingHom.map_det f C
  apply hf
  have h := det_add_ones_field (A.map f) (by
    rw [← hdet]
    exact (map_ne_zero_iff f hf).mpr hA)
  have hadj : (A.map f).adjugate = A.adjugate.map f := by
    have := RingHom.map_adjugate f A
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hsum : (A.map f + Matrix.of fun _ _ => (1 : K)) =
      (A + Matrix.of fun _ _ => (1 : R)).map f := by
    ext i j
    simp
  rw [hsum, ← hdet, ← hdet, hadj] at h
  rw [h, map_add, map_sum]
  simp [map_sum]

theorem entry (n : ℕ) (l : Fin n → ℂ) (a b : Fin n) :
    ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
        (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z)) a b =
      if a = b then Polynomial.X + Polynomial.C (l a)
      else if a < b then -1 else 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem adj_sum : ∀ (n : ℕ) (l : Fin n → ℂ), ∑ a, ∑ b, (Matrix.adjugate ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) + (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z))) a b = ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) - ∏ s, (Polynomial.X + Polynomial.C (l s)) := by
  intro n l
  set M : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
    (Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
      (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z) with hM
  have he : ∀ a b, M a b = if a = b then Polynomial.X + Polynomial.C (l a)
      else if a < b then -1 else 0 := entry n l
  have hdet : M.det = ∏ s, (Polynomial.X + Polynomial.C (l s)) := by
    rw [Matrix.det_of_upperTriangular]
    · exact Finset.prod_congr rfl fun s _ => by rw [he]; simp
    · intro i j hij
      have hij' : j < i := hij
      rw [he, if_neg (ne_of_gt hij'), if_neg (not_lt_of_gt hij')]
  have hdet1 : (M + Matrix.of fun _ _ => (1 : Polynomial ℂ)).det =
      ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) := by
    rw [Matrix.det_of_lowerTriangular]
    · exact Finset.prod_congr rfl fun s _ => by simp [he]
    · intro i j hij
      have hij' : i < j := hij
      simp [he, ne_of_lt hij', hij']
  have hne : M.det ≠ 0 := by
    rw [hdet, Finset.prod_ne_zero_iff]
    intro s _
    exact (Polynomial.monic_X_add_C (l s)).ne_zero
  have h := det_add_ones M hne
  rw [hdet1, hdet] at h
  rw [h]
  ring

end GlobalTheory.CompanionTheory.AdjSum
