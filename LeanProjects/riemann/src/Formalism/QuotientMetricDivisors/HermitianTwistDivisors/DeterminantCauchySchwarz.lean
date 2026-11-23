import Formalism.QuotientMetricDivisors.ProdFormula

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Formalism.DivisionValues

lemma one_le_det_one_add {m : Type*} [Fintype m] [DecidableEq m] {Z : Matrix m m ℂ}
    (hZ : Z.PosSemidef) : (1 : ℂ) ≤ (1 + Z).det := by
  have hspec := hZ.1.spectral_theorem
  have hUU : (hZ.1.eigenvectorUnitary : Matrix m m ℂ) * star (hZ.1.eigenvectorUnitary : Matrix m m ℂ) = 1 := by
    simp
  have hdet : ∀ x : Matrix m m ℂ, ((hZ.1.eigenvectorUnitary : Matrix m m ℂ) * x *
      star (hZ.1.eigenvectorUnitary : Matrix m m ℂ)).det = x.det := by
    intro x
    rw [det_mul, det_mul, mul_comm (det (hZ.1.eigenvectorUnitary : Matrix m m ℂ)), mul_assoc, ← det_mul, hUU,
      det_one, mul_one]
  have key : 1 + Z = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hZ.1.eigenvectorUnitary)
      (1 + diagonal (RCLike.ofReal ∘ hZ.1.eigenvalues)) := by
    rw [map_add, map_one, ← hspec]
  rw [key, Unitary.conjStarAlgAut_apply, hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have hev := hZ.eigenvalues_nonneg
  have hprod : ∏ i, ((1 : ℂ) + (RCLike.ofReal ∘ hZ.1.eigenvalues) i) =
      ((∏ i, (1 + hZ.1.eigenvalues i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, ← Complex.ofReal_one, Complex.real_le_real]
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => by linarith [hev i])

lemma det_le_det_add {m : Type*} [Fintype m] [DecidableEq m] {X Y : Matrix m m ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : X.det ≤ (X + Y).det := by
  by_cases hXu : IsUnit X
  · have hX0 : (0 : Matrix m m ℂ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
    have hSS : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X hX0
    have hS0 : (0 : Matrix m m ℂ) ≤ CFC.sqrt X := CFC.sqrt_nonneg X
    set S := CFC.sqrt X with hSdef
    have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS0
    have hSh : Sᴴ = S := hSpsd.1
    have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hSS ▸ hXu)
    have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
    have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
    have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
    have hTh : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSh]
    have hZ : ((S⁻¹)ᴴ * Y * S⁻¹).PosSemidef := hY.conjTranspose_mul_mul_same _
    have hmid : S * (S⁻¹ * Y * S⁻¹) * S = Y := by
      rw [← mul_assoc, ← mul_assoc, h1, one_mul, mul_assoc, h2, mul_one]
    have hsum : X + Y = S * (1 + (S⁻¹)ᴴ * Y * S⁻¹) * S := by
      rw [hTh, mul_add, add_mul, mul_one, hSS, hmid]
    have hdX : X.det = S.det * S.det := by rw [← hSS, det_mul]
    rw [hsum, det_mul, det_mul]
    have e : S.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det * S.det = X.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det := by
      rw [hdX]; ring
    rw [e]
    have hone := one_le_det_one_add hZ
    have hXd : 0 ≤ X.det := hX.det_nonneg
    have := mul_le_mul_of_nonneg_left hone hXd
    simpa using this
  · have hd : X.det = 0 := by
      by_contra h
      exact hXu ((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr h))
    rw [hd]
    exact (hX.add hY).det_nonneg

theorem determinant_cauchy_schwarz : DetCS := by
  intro n D Hc hHc A B
  have hHh : Hcᴴ = Hc := hHc.1
  have hPpsd : (A * Hc * Aᴴ).PosSemidef := hHc.posSemidef.mul_mul_conjTranspose_same A
  set P := A * Hc * Aᴴ with hP
  set Q := A * Hc * Bᴴ with hQ
  set R := B * Hc * Bᴴ with hR
  by_cases hPu : IsUnit P
  · have hPpd : P.PosDef := (hPpsd.posDef_iff_isUnit).mpr hPu
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
    have hPinv : (P⁻¹).PosSemidef := hPpd.inv.posSemidef
    have hPih : (P⁻¹)ᴴ = P⁻¹ := hPinv.1
    have hQh : Qᴴ = B * Hc * Aᴴ := by
      rw [hQ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]
    set K := B - Qᴴ * P⁻¹ * A with hK
    have hKpsd : (K * Hc * Kᴴ).PosSemidef := hHc.posSemidef.mul_mul_conjTranspose_same K
    have hXpsd : (Qᴴ * P⁻¹ * Q).PosSemidef := hPinv.conjTranspose_mul_mul_same Q
    have hKh : Kᴴ = Bᴴ - Aᴴ * P⁻¹ * Q := by
      rw [hK, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPih]
      simp only [Matrix.mul_assoc]
    have r1 : B * (Hc * Bᴴ) = R := by rw [hR, Matrix.mul_assoc]
    have r2 : ∀ X : Matrix (Fin D) (Fin D) ℂ, B * (Hc * (Aᴴ * X)) = Qᴴ * X := by
      intro X; rw [hQh]; simp only [Matrix.mul_assoc]
    have r3 : A * (Hc * Bᴴ) = Q := by rw [hQ, Matrix.mul_assoc]
    have r4 : ∀ X : Matrix (Fin D) (Fin D) ℂ, A * (Hc * (Aᴴ * X)) = P * X := by
      intro X; rw [hP]; simp only [Matrix.mul_assoc]
    have r5 : ∀ X : Matrix (Fin D) (Fin D) ℂ, P⁻¹ * (P * X) = X := by
      intro X; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet, one_mul]
    have hKK : K * Hc * Kᴴ = R - Qᴴ * P⁻¹ * Q := by
      rw [hKh, hK]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      rw [r2, r3, r4, r5, r1]
      abel
    have hsplit : R = Qᴴ * P⁻¹ * Q + K * Hc * Kᴴ := by rw [hKK]; abel
    have hle := det_le_det_add hXpsd hKpsd
    rw [← hsplit, det_mul, det_mul, det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hle
    obtain ⟨hpre, hpim⟩ := Complex.lt_def.mp hPpd.det_pos
    have key : ∀ pr : ℝ, star Q.det * (pr : ℂ)⁻¹ * Q.det = ((‖Q.det‖ ^ 2 / pr : ℝ) : ℂ) := by
      intro pr
      rw [mul_right_comm, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    have hpeq : P.det = ((P.det.re : ℝ) : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; simpa using hpim.symm)
    rw [hpeq, key] at hle
    have h2 := (Complex.le_def.mp hle).1
    rw [Complex.ofReal_re] at h2
    have hpre' : 0 < P.det.re := by simpa using hpre
    rw [div_le_iff₀ hpre'] at h2
    rw [mul_comm]
    exact h2
  · have hd : P.det = 0 := by
      by_contra h
      exact hPu ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr h))
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    have hw : v ᵥ* A = 0 := by
      by_contra hw
      have hsw : star (v ᵥ* A) ≠ 0 := star_ne_zero.mpr hw
      have hpos := hHc.dotProduct_mulVec_pos hsw
      have h0 : star (star (v ᵥ* A)) ⬝ᵥ (Hc *ᵥ star (v ᵥ* A)) = 0 := by
        rw [star_star]
        have h00 : (v ᵥ* P) ⬝ᵥ star v = 0 := by rw [hv, zero_dotProduct]
        rw [hP, ← vecMul_vecMul, ← vecMul_vecMul, ← dotProduct_mulVec, mulVec_conjTranspose, star_star,
          ← dotProduct_mulVec] at h00
        exact h00
      rw [h0] at hpos
      exact lt_irrefl _ hpos
    have hq : Q.det = 0 := by
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hv0, ?_⟩
      rw [hQ, ← vecMul_vecMul, ← vecMul_vecMul, hw, zero_vecMul, zero_vecMul]
    rw [hq, hd]
    simp

end Formalism.DivisionValues
