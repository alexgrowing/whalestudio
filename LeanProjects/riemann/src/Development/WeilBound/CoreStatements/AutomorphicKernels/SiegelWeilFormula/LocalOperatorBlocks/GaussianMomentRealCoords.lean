import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EvalMonomial2

noncomputable section

open MeasureTheory Complex MvPolynomial

namespace PositivityTheory.SiegelWeilFormula.KLI

theorem mer_symm (p : ℝ × ℝ) : Complex.measurableEquivRealProd.symm p = p.1 + p.2 * I := by
  rw [Complex.measurableEquivRealProd_symm_apply]
  apply Complex.ext <;> simp

def phi1 (sg : ℤˣ) (t z ξ : ℂ) (α β : ℕ) (w : ℂ) : ℂ :=
  w ^ α * star w ^ β * (cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z * (normSq w : ℂ)) *
    cexp (2 * Real.pi * I * ((t * (star ξ * w)).re : ℂ)))

def Rab (α β : ℕ) : MvPolynomial (Fin 2) ℂ := (X 0 + C I * X 1) ^ α * (X 0 - C I * X 1) ^ β

theorem deg_Rab (α β : ℕ) : (Rab α β).totalDegree ≤ α + β := by
  have h1 : (X 0 + C I * X 1 : MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp only [totalDegree_X, le_refl]
    · refine (totalDegree_mul _ _).trans ?_
      simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  have h2 : (X 0 - C I * X 1 : MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · simp only [totalDegree_X, le_refl]
    · refine (totalDegree_mul _ _).trans ?_
      simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  unfold PositivityTheory.SiegelWeilFormula.KLI.Rab
  refine (totalDegree_mul _ _).trans (add_le_add ?_ ?_)
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul le_rfl h1).trans_eq (mul_one _))
  · exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul le_rfl h2).trans_eq (mul_one _))

def lamF (t ξ : ℂ) : ℂ := 2 * Real.pi * I * ((t * star ξ).re : ℂ)

def muF (t ξ : ℂ) : ℂ := -(2 * Real.pi * I * ((t * star ξ).im : ℂ))

theorem gaussian_moment_real_coords (sg : ℤˣ) (t z ξ : ℂ) (α β : ℕ) (p : ℝ × ℝ) :
    phi1 sg t z ξ α β (p.1 + p.2 * I) =
      eval ![(p.1 : ℂ), (p.2 : ℂ)] (Rab α β) *
        G2 (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z) (lamF t ξ) (muF t ξ) p := by
  have hs : star ((p.1 : ℂ) + p.2 * I) = p.1 - p.2 * I := by
    apply Complex.ext <;> simp
  have hn : normSq ((p.1 : ℂ) + p.2 * I) = p.1 ^ 2 + p.2 ^ 2 := Complex.normSq_add_mul_I _ _
  have hre : (t * (star ξ * ((p.1 : ℂ) + p.2 * I))).re = p.1 * (t * star ξ).re - p.2 * (t * star ξ).im := by
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have h0 : (![(p.1 : ℂ), (p.2 : ℂ)] : Fin 2 → ℂ) 0 = p.1 := rfl
  have h1 : (![(p.1 : ℂ), (p.2 : ℂ)] : Fin 2 → ℂ) 1 = p.2 := rfl
  simp only [PositivityTheory.SiegelWeilFormula.KLI.phi1, PositivityTheory.SiegelWeilFormula.KLI.Rab, PositivityTheory.SiegelWeilFormula.KLI.G2, PositivityTheory.SiegelWeilFormula.KLI.lamF,
    PositivityTheory.SiegelWeilFormula.KLI.muF, hs, hn, hre, map_mul, map_pow, map_add, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X, h0, h1]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  · congr 1 <;> congr 1 <;> ring
  · congr 1
    push_cast
    ring

theorem integrable_gaussian_moment (sg : ℤˣ) (t z ξ : ℂ) (hz : 0 < ((sg : ℤ) : ℝ) * z.im) (α β : ℕ) :
    Integrable (phi1 sg t z ξ α β) := by
  have hB : (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z).re < 0 := by
    have hBeq : 2 * (Real.pi : ℂ) * I * ((sg : ℤ) : ℂ) * z = ((2 * Real.pi * ((sg : ℤ) : ℝ) : ℝ) : ℂ) * (I * z) := by
      push_cast
      ring
    rw [hBeq, Complex.re_ofReal_mul, Complex.I_mul_re]
    have := mul_pos Real.pi_pos hz
    nlinarith
  have h := PositivityTheory.SiegelWeilFormula.KLI.intg_poly2 hB (PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ) (PositivityTheory.SiegelWeilFormula.KLI.muF t ξ)
    (PositivityTheory.SiegelWeilFormula.KLI.Rab α β)
  rw [← (MeasurePreserving.symm Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [Function.comp_apply, PositivityTheory.SiegelWeilFormula.KLI.mer_symm,
    PositivityTheory.SiegelWeilFormula.KLI.gaussian_moment_real_coords]

theorem mom1 (sg : ℤˣ) (t : ℂ) (z : ℂ) (hz : 0 < ((sg : ℤ) : ℝ) * z.im) (α β : ℕ) :
    ∃ q : MvPolynomial Bool ℂ, q.totalDegree ≤ α + β ∧ ∀ ξ : ℂ,
      ∫ w : ℂ, phi1 sg t z ξ α β w =
        eval (fun b => if b then star ξ else ξ) q *
          cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * (-((normSq t : ℂ) / 4) * z⁻¹) * (normSq ξ : ℂ)) := by
  have hB : (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z).re < 0 := by
    have hBeq : 2 * (Real.pi : ℂ) * I * ((sg : ℤ) : ℂ) * z = ((2 * Real.pi * ((sg : ℤ) : ℝ) : ℝ) : ℂ) * (I * z) := by
      push_cast
      ring
    rw [hBeq, Complex.re_ofReal_mul, Complex.I_mul_re]
    have := mul_pos Real.pi_pos hz
    nlinarith
  have hS2 : ((sg : ℤ) : ℂ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or sg with h | h <;> simp [h]
  have hs0 : ((sg : ℤ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at hS2
    norm_num at hS2
  have hS : ((sg : ℤ) : ℂ) * ((sg : ℤ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hP : (Real.pi : ℂ) * (Real.pi : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hQ : I * I⁻¹ = 1 := mul_inv_cancel₀ Complex.I_ne_zero
  obtain ⟨R, hRdeg, hR⟩ := PositivityTheory.SiegelWeilFormula.KLI.mom2 hB (PositivityTheory.SiegelWeilFormula.KLI.Rab α β)
  obtain ⟨F, hF0, hF1⟩ : ∃ F : Fin 2 → MvPolynomial Bool ℂ,
      F 0 = C (2 * (Real.pi : ℂ) * I / 2) * (C t * X true + C (star t) * X false) ∧
      F 1 = C (-(2 * (Real.pi : ℂ) * I) / (2 * I)) * (C t * X true - C (star t) * X false) :=
    ⟨![C (2 * (Real.pi : ℂ) * I / 2) * (C t * X true + C (star t) * X false),
      C (-(2 * (Real.pi : ℂ) * I) / (2 * I)) * (C t * X true - C (star t) * X false)], rfl, rfl⟩
  have hF : ∀ i, (F i).totalDegree ≤ 1 := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [hF0]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;>
        refine (totalDegree_mul _ _).trans ?_ <;>
        simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
    · rw [hF1]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_) <;>
        refine (totalDegree_mul _ _).trans ?_ <;>
        simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  refine ⟨C (((Real.pi : ℂ) / -(2 * Real.pi * I * ((sg : ℤ) : ℂ) * z)) ^ (1 / 2 : ℂ) *
      ((Real.pi : ℂ) / -(2 * Real.pi * I * ((sg : ℤ) : ℂ) * z)) ^ (1 / 2 : ℂ)) * bind₁ F R, ?_, fun ξ => ?_⟩
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact ((PositivityTheory.SiegelWeilFormula.KLI.deg_bind_le F hF R).trans hRdeg).trans
      (PositivityTheory.SiegelWeilFormula.KLI.deg_Rab α β)
  · have hfun : (fun i => eval (fun b : Bool => if b then star ξ else ξ) (F i)) =
        ![PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ, PositivityTheory.SiegelWeilFormula.KLI.muF t ξ] := by
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · show eval (fun b : Bool => if b then star ξ else ξ) (F 0) = PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ
        rw [hF0]
        simp only [map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X, PositivityTheory.SiegelWeilFormula.KLI.lamF,
          Complex.re_eq_add_conj, Complex.star_def, Complex.conj_conj, ↓reduceIte, Bool.false_eq_true]
        ring
      · show eval (fun b : Bool => if b then star ξ else ξ) (F 1) = PositivityTheory.SiegelWeilFormula.KLI.muF t ξ
        rw [hF1]
        simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, PositivityTheory.SiegelWeilFormula.KLI.muF,
          Complex.im_eq_sub_conj, Complex.star_def, Complex.conj_conj, ↓reduceIte, Bool.false_eq_true]
        ring
    have heval : eval (fun b : Bool => if b then star ξ else ξ) (bind₁ F R) =
        eval ![PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ, PositivityTheory.SiegelWeilFormula.KLI.muF t ξ] R := by
      rw [← hfun]
      exact MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ) (fun b : Bool => if b then star ξ else ξ) F R
    have hn : (((t * star ξ).re : ℝ) : ℂ) ^ 2 + (((t * star ξ).im : ℝ) : ℂ) ^ 2 =
        (normSq t : ℂ) * (normSq ξ : ℂ) := by
      have h2 : normSq (star ξ) = normSq ξ := by rw [Complex.star_def, Complex.normSq_conj]
      have h1 : (t * star ξ).re ^ 2 + (t * star ξ).im ^ 2 = normSq t * normSq ξ := by
        rw [← h2, ← Complex.normSq_mul, Complex.normSq_apply]
        ring
      exact_mod_cast h1
    have hexp : -(PositivityTheory.SiegelWeilFormula.KLI.lamF t ξ ^ 2 / (4 * (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z))) +
        -(PositivityTheory.SiegelWeilFormula.KLI.muF t ξ ^ 2 / (4 * (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z))) =
        2 * Real.pi * I * ((sg : ℤ) : ℂ) * (-((normSq t : ℂ) / 4) * z⁻¹) * (normSq ξ : ℂ) := by
      unfold PositivityTheory.SiegelWeilFormula.KLI.lamF PositivityTheory.SiegelWeilFormula.KLI.muF
      linear_combination
        (-(1 / 2) * ((Real.pi : ℂ) * I * ((sg : ℤ) : ℂ)⁻¹ * z⁻¹ *
            ((((t * star ξ).re : ℝ) : ℂ) ^ 2 + (((t * star ξ).im : ℝ) : ℂ) ^ 2)) * I * I⁻¹) * hP +
        (-(1 / 2) * ((Real.pi : ℂ) * I * ((sg : ℤ) : ℂ)⁻¹ * z⁻¹ *
            ((((t * star ξ).re : ℝ) : ℂ) ^ 2 + (((t * star ξ).im : ℝ) : ℂ) ^ 2))) * hQ +
        (-(1 / 2) * (Real.pi : ℂ) * I * ((sg : ℤ) : ℂ)⁻¹ * z⁻¹) * hn +
        ((1 / 2) * (Real.pi : ℂ) * I * z⁻¹ * ((normSq t : ℂ) * (normSq ξ : ℂ)) * ((sg : ℤ) : ℂ)⁻¹) * hS2 +
        (-(1 / 2) * (Real.pi : ℂ) * I * z⁻¹ * ((normSq t : ℂ) * (normSq ξ : ℂ)) * ((sg : ℤ) : ℂ)) * hS
    have hchg : ∫ w : ℂ, PositivityTheory.SiegelWeilFormula.KLI.phi1 sg t z ξ α β w =
        ∫ p : ℝ × ℝ, PositivityTheory.SiegelWeilFormula.KLI.phi1 sg t z ξ α β (Complex.measurableEquivRealProd.symm p) :=
      ((MeasurePreserving.symm Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod).integral_comp
        Complex.measurableEquivRealProd.symm.measurableEmbedding _).symm
    rw [hchg]
    simp only [PositivityTheory.SiegelWeilFormula.KLI.mer_symm, PositivityTheory.SiegelWeilFormula.KLI.gaussian_moment_real_coords]
    rw [hR, PositivityTheory.SiegelWeilFormula.KLI.J_zero hB, PositivityTheory.SiegelWeilFormula.KLI.J_zero hB, map_mul,
      MvPolynomial.eval_C, heval, ← hexp, Complex.exp_add]
    ring

end PositivityTheory.SiegelWeilFormula.KLI

end
