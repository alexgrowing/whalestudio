import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralIdempotentLiftNewtonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixDecomposeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormDetOneAddSmulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommutantValuationDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientIntegralUnitStatement

open Matrix

namespace GlobalTheory.UnitDiscAlg

theorem unit_split {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] {n : ℕ} {N : Matrix (Fin n) (Fin n) E} {ϖ : E}
    (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hB : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1) (hϖ : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖)
    (hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x)
    (y : Matrix (Fin n) (Fin n) E) (hyN : y * N = N * y) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧
      e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a := by
  obtain ⟨x, z, a₁, a₂, a₃, ⟨hxN, hzN, h1N, h2N, h3N⟩, hint, hx, hyx, hyz⟩ :=
    GlobalTheory.T.commuting_integral_matrix_decompose E n N ϖ hN hB h0 h1 hϖ y hyN hy
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  obtain ⟨e, a', heN, ha'N, he, heI, ha'I, hea⟩ :=
    GlobalTheory.T.exists_integral_idempotent_lift_newton E n N x a₁ ϖ h1 hxN (fun i j => (hint i j).1) (fun i j => (hint i j).2.2.1) hx
  have hzI : ∀ i j, ‖z i j‖ ≤ 1 := fun i j => (hint i j).2.1
  have ha₂I : ∀ i j, ‖a₂ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.1
  have ha₃I : ∀ i j, ‖a₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.2
  refine ⟨e, a₂ - y * a', heN, ?_, fun i j => ⟨heI i j, integ_sub ha₂I (integ_mul hy ha'I) i j⟩,
    he, ?_, ?_⟩
  · rw [sub_mul, mul_sub, h2N, Matrix.mul_assoc, ha'N, ← Matrix.mul_assoc, hyN, Matrix.mul_assoc]
  ·
    have hye : y * e = e * y := hcomm y e hyN heN
    have hze : z * e = e * z := hcomm z e hzN heN
    have hyz' : y * z = z * y := hcomm y z hyN hzN
    have hprod : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + ϖ • (a₃ + y * z * a' - a') := by
      have e1 : e = x + ϖ • a' := by rw [← hea]; abel
      have e2 : y * z * x = x + ϖ • a₃ := by rw [← hyz]; abel
      have key : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + y * z * e - e := by
        have : (y * e + (1 - e)) * (z * e + (1 - e)) =
            y * (e * z) * e + y * e * (1 - e) + (1 - e) * z * e + (1 - e) * (1 - e) := by
          noncomm_ring
        rw [this, ← hze]
        have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have hee' : (1 - e) * z * e = 0 := by
          rw [Matrix.mul_assoc, hze, ← Matrix.mul_assoc, sub_mul, one_mul, he, sub_self,
            Matrix.zero_mul]
        have hee'' : (1 - e) * (1 - e) = 1 - e := by
          rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
        rw [Matrix.mul_assoc y e (1 - e), hee, Matrix.mul_zero, hee', hee'',
          ← Matrix.mul_assoc, Matrix.mul_assoc (y * z) e e, he]
        abel
      rw [key]
      conv_lhs => rw [e1]
      rw [Matrix.mul_add, e2, Matrix.mul_smul]
      simp only [smul_add, smul_sub]
      abel
    have hwI : ∀ i j, ‖(y * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hy heI) (integ_sub integ_one heI)
    have hw'I : ∀ i j, ‖(z * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hzI heI) (integ_sub integ_one heI)
    have hd := congrArg (fun m => ‖m.det‖) hprod
    simp only [Matrix.det_mul, norm_mul] at hd
    rw [GlobalTheory.T.ultrametric_norm_det_one_add_smul E n _ ϖ h1 (integ_sub (integ_add ha₃I (integ_mul (integ_mul hy hzI) ha'I)) ha'I)]
      at hd
    have ha := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hwI
    have hb := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hw'I
    nlinarith [norm_nonneg (y * e + (1 - e)).det, norm_nonneg (z * e + (1 - e)).det]
  · have : y * (1 - e) = y * (1 - x) - y * (e - x) := by noncomm_ring
    rw [this, hyx, hea, Matrix.mul_smul, ← smul_sub]

theorem units_quotient : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N c b : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  intro E _ _ _ n N c b ϖ hN hB h0 h1 hϖ hc hcN hbN hb hbd
  have hB' : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1 := by
    obtain ⟨u, v, -, -, h⟩ := hB
    exact ⟨u, v, h⟩
  have hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x :=
    fun x y hx hy => comm_of_bezout hB' hx hy
  obtain ⟨e₁, e₂, e₃, u, a₂, a₃, hN6, hI6, hu, h11, h22, h33, h12, h13, h23, hs, hc1, hc2, hc3⟩ :=
    GlobalTheory.T.matrix_commutant_valuation_decomposition E n N ϖ h0 h1 hcomm (unit_split hN hB h0 h1 hϖ hcomm) c hc hcN
  exact GlobalTheory.T.quotient_integral_unit_alt E n N c b e₁ e₂ e₃ u a₂ a₃ ϖ h0 h1 hcomm hc hcN hbN hb hbd hN6 hI6 hu h11 h22 h33
    h12 h13 h23 hs hc1 hc2 hc3

end GlobalTheory.UnitDiscAlg
