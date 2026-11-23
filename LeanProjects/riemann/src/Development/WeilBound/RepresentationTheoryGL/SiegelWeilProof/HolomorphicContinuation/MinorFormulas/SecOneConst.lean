import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.WROrdA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussM
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.HermTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ}

theorem vM_eq_uM (s : ℂ) (y : E n) : vM s y = uM (-s) y := by
  simp only [vM, uM, mul_neg, neg_smul, sub_neg_eq_add]

theorem sec_one_const (b : Bool) {c t : ℝ} (hc : 0 < c) (y : E n) :
    secN (fun _ : Fin m => b) c t 1 (herm y) =
      (((Real.pi : ℂ) / c) ^ n) ^ m * (if b then uM ((t / c : ℝ) : ℂ) y else vM ((t / c : ℝ) : ℂ) y).det ^ m := by
  have hH : (herm y).IsHermitian := PositivityTheory.Rg.Sw.WR.G.GM.herm_isHermitian y
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [PositivityTheory.Rg.Sw.WR.G.base m n (fun _ => b) c t hc (herm y) hH]
  cases b with
  | true =>
    simp only [PositivityTheory.Rg.Sw.WR.G.Amat, PositivityTheory.Rg.Sw.sgn, ↓reduceIte, mul_one]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]
    congr 1
    have e : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * (t : ℂ)) • (herm y)ᵀ
        = ((c : ℂ) • (1 - (Complex.I * ((t / c : ℝ) : ℂ)) • herm y))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
        smul_sub, smul_smul, smul_one_eq_diagonal]
      congr 2
      push_cast
      field_simp
    rw [e, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin, uM, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv', div_pow]
    ring
  | false =>
    simp only [PositivityTheory.Rg.Sw.WR.G.Amat, PositivityTheory.Rg.Sw.sgn, Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]
    congr 1
    have e : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (-(Complex.I * (t : ℂ))) • (herm y)ᵀ
        = ((c : ℂ) • (1 + (Complex.I * ((t / c : ℝ) : ℂ)) • herm y))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
        smul_add, smul_smul, neg_smul, sub_neg_eq_add]
      congr 2
      push_cast
      field_simp
    rw [e, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin, vM, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv', div_pow]
    ring

theorem cls_vac (s z : ℂ) (y : E n) :
    cls s z m 0 1 y = ((dP y : ℝ) : ℂ) ^ (-z) * (uM s y).det ^ m := by
  unfold cls evUV
  simp

theorem integrand_eq (b : Bool) {c t : ℝ} (hc : 0 < c) (z : ℂ) (y : E n) :
    ((dP y : ℝ) : ℂ) ^ (-z) * secN (fun _ : Fin m => b) c t 1 (herm y) =
      (((Real.pi : ℂ) / c) ^ n) ^ m *
        cls (if b then ((t / c : ℝ) : ℂ) else -((t / c : ℝ) : ℂ)) z m 0 1 y := by
  rw [sec_one_const b hc, cls_vac]
  cases b
  · simp only [Bool.false_eq_true, if_false, vM_eq_uM]
    ring
  · simp only [if_true]
    ring

theorem wrOrd_of (hS : SPrime) : PositivityTheory.SiegelWeilFormula.Gen.WROrd := by
  intro m n hmn b c t hc ht β hβ
  have hc0 : c ≠ 0 := hc.ne'
  have hs1 : (if b then ((t / c : ℝ) : ℂ) else -((t / c : ℝ) : ℂ)) = 1 ∨
      (if b then ((t / c : ℝ) : ℂ) else -((t / c : ℝ) : ℂ)) = -1 := by
    rcases ht with rfl | rfl <;> cases b <;> simp [hc0, neg_div]
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc0
    · exact neg_ne_zero.mpr hc0
  obtain ⟨W, hW, ⟨σ₀, hσ⟩, hder⟩ := hS n m _ hs1 hmn t ht0 β hβ
  obtain ⟨g, hg, hWg⟩ := entire_factor W hW (n - m) hder
  refine ⟨fun z => (((Real.pi : ℂ) / c) ^ n) ^ m * g z, (differentiable_const _).mul hg, σ₀, fun z hz => ?_⟩
  obtain ⟨hI, hWz⟩ := hσ z hz
  have hfun : (fun y : E n => ((dP y : ℝ) : ℂ) ^ (-z) * secN (fun _ : Fin m => b) c t 1 (herm y) * chr t β y)
      = fun y => (((Real.pi : ℂ) / c) ^ n) ^ m *
        (cls (if b then ((t / c : ℝ) : ℂ) else -((t / c : ℝ) : ℂ)) z m 0 1 y * chr t β y) := by
    funext y
    rw [integrand_eq (m := m) b hc z y]
    ring
  rw [hfun]
  refine ⟨hI.const_mul _, ?_⟩
  rw [integral_const_mul, ← hWz, hWg z]
  ring

end PositivityTheory.Rg.Sw.SP
