import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pCharConj_of :
    UpperTheory.Gal.CertificateRingHomMap.CharConj := by
  intro E _ _ _ n y P s h φ t ht
  set A : Matrix (Fin n) (Fin n) ℂ := (y : Matrix (Fin n) (Fin n) E).map φ with hAdef
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) E).map φ with hQdef
  set B : Matrix (Fin n) (Fin n) ℂ :=
    (y : Matrix (Fin n) (Fin n) E).map (NumberField.ComplexEmbedding.conjugate φ) with hBdef
  have hB : B = ((y : Matrix (Fin n) (Fin n) E).map (IsCMField.complexConj E)).map φ := by
    ext i j
    simp only [B, Matrix.map_apply]
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq,
      NumberField.IsCMField.complexEmbedding_complexConj]
  have hrel : Bᵀ * Q * A = ((s : ℚ) : ℂ) • Q := by
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map φ) h
    simp only [Matrix.map_mul] at h2
    rw [Matrix.transpose_map] at h2
    rw [hB, hQdef, hAdef, h2]
    ext i j
    simp [Matrix.map_apply]
  have hA : ((y : Matrix (Fin n) (Fin n) E).map φ).charpoly = ∏ i, (X - C (t i)) := by
    rw [Matrix.charpoly_map]; exact ht
  have hdetA : A.det ≠ 0 := by
    have hu : IsUnit (y : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
    rw [hAdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hu.ne_zero
  have hdetQ : Q.det ≠ 0 := by
    have hu : IsUnit (P : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
    rw [hQdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hu.ne_zero
  have hprodt : A.det = ∏ i, t i := by
    have e := congrArg (Polynomial.eval 0) hA
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at e
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub] at e
    rw [map_zero, zero_sub, Matrix.det_neg, Fintype.card_fin] at e
    have e2 : ∏ i, -t i = (-1) ^ n * ∏ i, t i := by
      calc ∏ i, -t i = ∏ i, ((-1) * t i) := by simp
        _ = (-1) ^ n * ∏ i, t i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [e2] at e
    exact mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) e
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i hi
    apply hdetA
    rw [hprodt]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hpt : ∏ i, t i ≠ 0 := hprodt ▸ hdetA
  refine ⟨ht0, ?_⟩
  rw [← Matrix.charpoly_map]
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := {z : ℂ | z ≠ 0})
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    have key : (Matrix.scalar (Fin n) z - B).det * A.det =
        z ^ n * (-1) ^ n * (Matrix.scalar (Fin n) (((s : ℚ) : ℂ) / z) - A).det := by
      have e1 : (Matrix.scalar (Fin n) z - Bᵀ) * Q * A = Q * (z • A - ((s : ℚ) : ℂ) • 1) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_mul, sub_mul, hrel, mul_sub]
        simp [smul_mul_assoc, mul_smul_comm]
      have e2 : (Matrix.scalar (Fin n) z - B).det = (Matrix.scalar (Fin n) z - Bᵀ).det := by
        rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, Matrix.charpoly_transpose]
      have e3 : z • A - ((s : ℚ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
          z • (-(Matrix.scalar (Fin n) (((s : ℚ) : ℂ) / z) - A)) := by
        rw [neg_sub, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul,
          mul_div_cancel₀ _ hz]
      have e4 := congrArg Matrix.det e1
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, e3, Matrix.det_smul, Matrix.det_neg,
        Fintype.card_fin, ← e2] at e4
      apply mul_left_cancel₀ hdetQ
      linear_combination e4
    have hAev := congrArg (Polynomial.eval (((s : ℚ) : ℂ) / z)) hA
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at hAev
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hAev
    rw [hAev, hprodt] at key
    rw [Matrix.eval_charpoly, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hfac : ∀ i, (z - ((s : ℚ) : ℂ) / t i) * t i = (z * -1) * (((s : ℚ) : ℂ) / z - t i) := by
      intro i
      field_simp [ht0 i, hz]
      ring
    have hq : (∏ i, (z - ((s : ℚ) : ℂ) / t i)) * ∏ i, t i =
        z ^ n * (-1) ^ n * ∏ i, (((s : ℚ) : ℂ) / z - t i) := by
      rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => hfac i),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    exact mul_right_cancel₀ hpt (key.trans hq.symm)
  · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
