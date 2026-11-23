import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.DivClosedOf

noncomputable section

namespace Formalism.L2.SG.Pf.ColDictValCPf

open Matrix MvPolynomial
open scoped ComplexOrder

namespace DensPf

variable {n : ℕ}

theorem cayley_isometry (G A : Matrix (Fin n) (Fin n) ℂ) (hskew : Aᴴ * G = -(G * A))
    (hB : IsUnit (1 + A).det) :
    ((1 - A) * (1 + A)⁻¹)ᴴ * G * ((1 - A) * (1 + A)⁻¹) = G := by
  have h1 : (1 - Aᴴ) * G = G * (1 + A) := by
    rw [sub_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hskew, sub_neg_eq_add]
  have h2 : G * (1 - A) = (1 + Aᴴ) * G := by
    rw [mul_sub, add_mul, Matrix.one_mul, Matrix.mul_one, hskew, sub_eq_add_neg]
  have h3 : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by noncomm_ring
  have hBH : IsUnit (1 + Aᴴ).det := by
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + Aᴴ = (1 + A)ᴴ by
      rw [conjTranspose_add, conjTranspose_one], det_conjTranspose]
    exact hB.star
  rw [conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_add,
    conjTranspose_one]
  calc (1 + Aᴴ)⁻¹ * (1 - Aᴴ) * G * ((1 - A) * (1 + A)⁻¹)
      = (1 + Aᴴ)⁻¹ * ((1 - Aᴴ) * G) * (1 - A) * (1 + A)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (1 + Aᴴ)⁻¹ * (G * (1 - A)) * ((1 + A) * (1 + A)⁻¹) := by
        rw [h1]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (1 + A), h3]
        simp only [Matrix.mul_assoc]
    _ = (1 + Aᴴ)⁻¹ * ((1 + Aᴴ) * G) := by rw [h2, mul_nonsing_inv _ hB, Matrix.mul_one]
    _ = G := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hBH, Matrix.one_mul]

theorem skew_of (G P : Matrix (Fin n) (Fin n) ℂ) (hH : Gᴴ = G) (hG : IsUnit G.det) :
    (P - G⁻¹ * Pᴴ * G)ᴴ * G = -(G * (P - G⁻¹ * Pᴴ * G)) := by
  have hi : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hH]
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hi, hH]
  simp only [sub_mul, mul_sub, Matrix.mul_assoc, nonsing_inv_mul _ hG, Matrix.mul_one]
  rw [← Matrix.mul_assoc G G⁻¹, mul_nonsing_inv _ hG, Matrix.one_mul]
  abel

def Pm (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Bool × Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => X (true, i, j) + C Complex.I * X (false, i, j)

def Qm (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Bool × Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => X (true, j, i) - C Complex.I * X (false, j, i)

def Lp (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (MvPolynomial (Bool × Fin n × Fin n) ℂ) :=
  Pm n - G⁻¹.map C * Qm n * G.map C

def Mp (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (MvPolynomial (Bool × Fin n × Fin n) ℂ) :=
  (1 - Lp G) * adjugate (1 + Lp G)

def dp (G : Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (Bool × Fin n × Fin n) ℂ := det (1 + Lp G)

def hq (G : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial (Bool × Fin n × Fin n) ℂ :=
  ∑ d ∈ p.support, C (p.coeff d) * dp G ^ (p.totalDegree - d.degree) *
    ∏ i : Fin n × Fin n, Mp G i.1 i.2 ^ d i

theorem map_C_mat (z : Bool × Fin n × Fin n → ℂ) (H : Matrix (Fin n) (Fin n) ℂ) :
    (eval z).mapMatrix (H.map C) = H := by
  ext i j; simp [RingHom.mapMatrix_apply]

theorem map_Lp (G : Matrix (Fin n) (Fin n) ℂ) (z : Bool × Fin n × Fin n → ℂ) :
    (eval z).mapMatrix (Lp G) =
      Matrix.of (fun i j => z (true, i, j) + Complex.I * z (false, i, j)) -
        G⁻¹ * Matrix.of (fun i j => z (true, j, i) - Complex.I * z (false, j, i)) * G := by
  have hP : (eval z).mapMatrix (Pm n) = Matrix.of (fun i j => z (true, i, j) + Complex.I * z (false, i, j)) := by
    ext i j; simp [Pm, RingHom.mapMatrix_apply]
  have hQ : (eval z).mapMatrix (Qm n) = Matrix.of (fun i j => z (true, j, i) - Complex.I * z (false, j, i)) := by
    ext i j; simp [Qm, RingHom.mapMatrix_apply]
  rw [Lp, map_sub, map_mul, map_mul, hP, hQ, map_C_mat, map_C_mat]

theorem eval_dp (G : Matrix (Fin n) (Fin n) ℂ) (z : Bool × Fin n × Fin n → ℂ) :
    eval z (dp G) = det (1 + (eval z).mapMatrix (Lp G)) := by
  rw [dp, RingHom.map_det, map_add, map_one]

theorem eval_hq (G : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ)
    (z : Bool × Fin n × Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : (eval z).mapMatrix (Lp G) = A)
    (hd : det (1 + A) ≠ 0) :
    eval z (hq G p) = det (1 + A) ^ p.totalDegree *
      eval (fun x => ((1 - A) * (1 + A)⁻¹) x.1 x.2) p := by
  have hMm : (eval z).mapMatrix (Mp G) = (1 - A) * adjugate (1 + A) := by
    rw [Mp, map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one, hA]
  have hM : ∀ i j, eval z (Mp G i j) = det (1 + A) * ((1 - A) * (1 + A)⁻¹) i j := by
    intro i j
    have h2 : (1 - A) * (1 + A)⁻¹ = (det (1 + A))⁻¹ • ((1 - A) * adjugate (1 + A)) := by
      rw [inv_def, Ring.inverse_eq_inv', Matrix.mul_smul]
    rw [h2, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul, ← hMm]
    rfl
  have hdz : eval z (dp G) = det (1 + A) := by rw [eval_dp, hA]
  rw [hq, map_sum]
  conv_rhs => rw [eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hdm => ?_
  simp only [map_mul, map_pow, map_prod, eval_C, hdz, hM, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hle : d.degree ≤ p.totalDegree := le_totalDegree hdm
  rw [← Finsupp.degree_eq_sum,
    show det (1 + A) ^ p.totalDegree = det (1 + A) ^ (p.totalDegree - d.degree) * det (1 + A) ^ d.degree by
      rw [← pow_add, Nat.sub_add_cancel hle]]
  ring

end DensPf

open DensPf in
theorem density_holds : Dens := by
  intro n G hGpd p hp g hg
  have hH : Gᴴ = G := hGpd.1
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hGpd.isUnit
  have hzero : hq G p * dp G = 0 := by
    apply funext_set (fun _ => Set.range Complex.ofReal)
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro z hz
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_range, true_implies] at hz
    choose r hr using hz
    have hz' : z = fun v => (r v : ℂ) := funext fun v => (hr v).symm
    subst hz'
    set P : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of (fun i j => (r (true, i, j) : ℂ) + Complex.I * r (false, i, j)) with hPdef
    have hA : (eval (fun v => (r v : ℂ))).mapMatrix (Lp G) = P - G⁻¹ * Pᴴ * G := by
      rw [map_Lp]
      congr 3
      ext i j
      simp only [hPdef, conjTranspose_apply, of_apply, star_add, star_mul', Complex.star_def,
        Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [map_zero, map_mul]
    by_cases hd : det (1 + (P - G⁻¹ * Pᴴ * G)) = 0
    · rw [eval_dp, hA, hd, mul_zero]
    · rw [eval_hq G p _ _ hA hd, hp _ (cayley_isometry G _ (skew_of G P hH hGu) (isUnit_iff_ne_zero.2 hd)),
        mul_zero, zero_mul]
  have hB : (1 + g) * (1 + g)⁻¹ = 1 := mul_nonsing_inv _ hg
  have hB' : (1 + g)⁻¹ * (1 + g) = 1 := nonsing_inv_mul _ hg
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin n) (Fin n) ℂ, Y = (1 - g) * (1 + g)⁻¹ := ⟨_, rfl⟩
  have hY1 : 1 + Y = (2 : ℂ) • (1 + g)⁻¹ := by
    calc 1 + Y = (1 + g) * (1 + g)⁻¹ + (1 - g) * (1 + g)⁻¹ := by rw [hB, hY]
      _ = ((1 + g) + (1 - g)) * (1 + g)⁻¹ := by rw [← add_mul]
      _ = (2 : ℂ) • (1 + g)⁻¹ := by
        rw [show (1 + g) + (1 - g) = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) by rw [two_smul]; abel,
          Matrix.smul_mul, Matrix.one_mul]
  have hY2 : 1 - Y = (2 : ℂ) • (g * (1 + g)⁻¹) := by
    calc 1 - Y = (1 + g) * (1 + g)⁻¹ - (1 - g) * (1 + g)⁻¹ := by rw [hB, hY]
      _ = ((1 + g) - (1 - g)) * (1 + g)⁻¹ := by rw [← sub_mul]
      _ = (2 : ℂ) • (g * (1 + g)⁻¹) := by
        rw [show (1 + g) - (1 - g) = (2 : ℂ) • g by rw [two_smul]; abel, Matrix.smul_mul]
  have hR : (1 + Y) * ((1 / 2 : ℂ) • (1 + g)) = 1 := by
    rw [hY1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB']
    norm_num
  have hYu : IsUnit (1 + Y).det := isUnit_det_of_right_inverse hR
  have hcay : (1 - Y) * (1 + Y)⁻¹ = g := by
    rw [inv_eq_right_inv hR, hY2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hB',
      Matrix.mul_one]
    norm_num
  let z0 : Bool × Fin n × Fin n → ℂ := fun v => if v.1 then Y v.2.1 v.2.2 / 2
    else -Complex.I * Y v.2.1 v.2.2 / 2
  have hA0 : (eval z0).mapMatrix (Lp G) = Y := by
    rw [map_Lp]
    have hP0 : Matrix.of (fun i j => z0 (true, i, j) + Complex.I * z0 (false, i, j)) = Y := by
      ext i j
      simp only [z0, of_apply, if_true, Bool.false_eq_true, if_false]
      linear_combination (-(Y i j) / 2) * Complex.I_sq
    have hQ0 : Matrix.of (fun i j => z0 (true, j, i) - Complex.I * z0 (false, j, i)) = 0 := by
      ext i j
      simp only [z0, of_apply, if_true, Bool.false_eq_true, if_false, Matrix.zero_apply]
      linear_combination (Y j i / 2) * Complex.I_sq
    rw [hP0, hQ0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
  have hd0 : det (1 + Y) ≠ 0 := hYu.ne_zero
  have h := congrArg (eval z0) hzero
  rw [map_mul, map_zero, eval_hq G p z0 Y hA0 hd0, eval_dp, hA0, hcay] at h
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h (pow_ne_zero _ hd0)
    · exact h
  · exact absurd h hd0

end Formalism.L2.SG.Pf.ColDictValCPf
