import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem splitCore {n : ℕ} {B : Type*} [CommRing B] (s : B →+* B) (e e' : B)
    (hee' : e * e' = 0) (hsum : e + e' = 1) (hse : s e = e') (hse' : s e' = e)
    (G G' Gi : Matrix (Fin n) (Fin n) B) (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hG : (G.map s)ᵀ = G) (hG' : (G'.map s)ᵀ = G') (hdet : IsUnit G'.det) :
    ∃ P : Matrix (Fin n) (Fin n) B, IsUnit P.det ∧ G' = Pᵀ * G * P.map s := by
  classical
  have hs1 : (G.map s) * (Gi.map s) = 1 := by
    rw [← Matrix.map_mul, hGGi, Matrix.map_one s s.map_zero s.map_one]
  have hsGi : (Gi.map s)ᵀ = Gi := by
    have h2 : (Gi.map s)ᵀ * G = 1 := by
      have := congrArg Matrix.transpose hs1
      rwa [Matrix.transpose_mul, hG, Matrix.transpose_one] at this
    calc (Gi.map s)ᵀ = (Gi.map s)ᵀ * (G * Gi) := by rw [hGGi, Matrix.mul_one]
      _ = ((Gi.map s)ᵀ * G) * Gi := by rw [Matrix.mul_assoc]
      _ = Gi := by rw [h2, Matrix.one_mul]
  have hA : ((G' * Gi)ᵀ).map s = Gi * G' := by
    rw [Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hsGi, hG']
  have hee : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [hsum, hee', mul_one, sub_zero]
  have he'e' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e * e' := by ring
      _ = e' := by rw [hsum, hee', mul_one, sub_zero]
  have he'e : e' * e = 0 := by rw [mul_comm, hee']
  have hu : IsUnit G'.det := hdet
  set A : Matrix (Fin n) (Fin n) B := (G' * Gi)ᵀ with hAdef
  set Ai : Matrix (Fin n) (Fin n) B := (G * G'⁻¹)ᵀ with hAidef
  have hAAi : A * Ai = 1 := by
    rw [hAdef, hAidef, ← Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc G'⁻¹,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, hGGi, Matrix.transpose_one]
  refine ⟨e • A + e' • 1, ?_, ?_⟩
  · apply Matrix.isUnit_det_of_right_inverse (B := e • Ai + e' • 1)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
      Matrix.mul_one, Matrix.one_mul, hAAi, hee, he'e', hee', he'e, zero_smul, add_zero, zero_add]
    first
      | rw [← add_smul, hsum, one_smul]
      | rw [add_comm, ← add_smul, hsum, one_smul]
  · have hP : (e • A + e' • (1 : Matrix (Fin n) (Fin n) B)).map s = e' • (Gi * G') + e • 1 := by
      rw [Matrix.map_add _ (map_add s), Matrix.map_smul' _ _ _ (map_mul s),
        Matrix.map_smul' _ _ _ (map_mul s), hA, Matrix.map_one s s.map_zero s.map_one, hse, hse']
    rw [hP]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hAdef,
      Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hGiG, hGGi,
      ← Matrix.mul_assoc Gi G, ← Matrix.mul_assoc G Gi, hee, he'e', hee', he'e, zero_smul,
      add_zero, zero_add]
    first
      | rw [← add_smul, hsum, one_smul]
      | rw [add_comm, ← add_smul, hsum, one_smul]

theorem UpperTheory.Gal.G1.pSplitCongr :
    SplitCongr := by
  intro E _ _ _ n N N' hN hN' hN0 hN'0 K _ _ θ D hD hθc hθ r hr
  set σ := IsCMField.complexConj E with hσeq
  set R : E →ₐ[maximalRealSubfield E] K ⊗[maximalRealSubfield E] E :=
    Algebra.TensorProduct.includeRight with hReq
  set L : K →ₐ[maximalRealSubfield E] K ⊗[maximalRealSubfield E] E :=
    Algebra.TensorProduct.includeLeft with hLeq
  set sB := GlobalTheory.HermGlobal.baseConj σ K with hsBeq
  have hsL : ∀ a : K, sB (L a) = L a := by
    intro a
    simp [hsBeq, hLeq, GlobalTheory.HermGlobal.baseConj]
  have hsR : ∀ x : E, sB (R x) = R (σ x) := by
    intro x
    simp [hsBeq, hReq, GlobalTheory.HermGlobal.baseConj]
  have hDE : (D : E) ≠ 0 := Int.cast_ne_zero.mpr hD
  set w := L r * R (θ / D) with hweq
  have hww : w * w = 1 := by
    have h1 : L r * L r = R (D : E) := by
      rw [← map_mul, ← sq, hr, map_intCast, map_intCast]
    calc w * w = (L r * L r) * (R (θ / D) * R (θ / D)) := by rw [hweq]; ring
      _ = R ((D : E) * (θ / D * (θ / D))) := by rw [h1, ← map_mul, ← map_mul]
      _ = 1 := by
        rw [div_mul_div_comm, ← sq θ, hθ]
        rw [show (D : E) * ((D : E) / (D * D)) = 1 by field_simp]
        exact map_one R
  have hsw : sB w = -w := by
    rw [hweq, map_mul, hsL, hsR, map_div₀, hθc, map_intCast, neg_div, map_neg, mul_neg]
  set h := R (2 : E)⁻¹ with hheq
  have hsh : sB h = h := by
    rw [hheq, hsR, map_inv₀, map_ofNat]
  have h2 : h * 2 = 1 := by
    rw [hheq, show (2 : K ⊗[maximalRealSubfield E] E) = R 2 from (map_ofNat R 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero), map_one]
  set e := h * (1 + w) with heeq
  set e' := h * (1 - w) with he'eq
  have hee' : e * e' = 0 := by
    calc e * e' = h * h * (1 - w * w) := by rw [heeq, he'eq]; ring
      _ = 0 := by rw [hww, sub_self, mul_zero]
  have hsum : e + e' = 1 := by
    calc e + e' = h * 2 := by rw [heeq, he'eq]; ring
      _ = 1 := h2
  have hse : sB e = e' := by
    rw [heeq, he'eq, map_mul, map_add, map_one, hsh, hsw, sub_eq_add_neg]
  have hse' : sB e' = e := by
    rw [heeq, he'eq, map_mul, map_sub, map_one, hsh, hsw, sub_neg_eq_add]
  have hNu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN0
  have hN'u : IsUnit N'.det := isUnit_iff_ne_zero.mpr hN'0
  have hGGi : N.map R * N⁻¹.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv N hNu, Matrix.map_one _ (map_zero R) (map_one R)]
  have hGiG : N⁻¹.map R * N.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul N hNu, Matrix.map_one _ (map_zero R) (map_one R)]
  have hG'G'i : N'.map R * N'⁻¹.map R = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv N' hN'u, Matrix.map_one _ (map_zero R) (map_one R)]
  have hG : ((N.map R).map sB.toRingHom)ᵀ = N.map R := by
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact (hsR _).trans (congrArg R (hN b a))
  have hG' : ((N'.map R).map sB.toRingHom)ᵀ = N'.map R := by
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact (hsR _).trans (congrArg R (hN' b a))
  obtain ⟨P, hP, hPe⟩ := splitCore sB.toRingHom e e' hee' hsum hse hse' (N.map R) (N'.map R)
    (N⁻¹.map R) hGGi hGiG hG hG' (Matrix.isUnit_det_of_right_inverse hG'G'i)
  refine ⟨P, hP, ?_⟩
  exact hPe
