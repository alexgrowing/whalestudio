import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.RealWeil

theorem dRho_apply_basis {l : Type} [Fintype l] [DecidableEq l] (w : l ⊕ l → ℝ) (f : Sch l)
    (x : EuclideanSpace ℝ l) :
    dRho w f x = ∑ b, (w (.inl b) : ℂ) * fderiv ℝ f x (EuclideanSpace.single b 1) +
      2 * π * I * (∑ b, (w (.inr b) : ℂ) * (x b : ℂ)) * f x := by
  rw [dRho_apply]
  have h1 : pPart w = ∑ b, w (.inl b) • EuclideanSpace.single b (1 : ℝ) := by
    ext i
    simp [pPart, EuclideanSpace.single_apply, Pi.single_apply]
  have h2 : inner ℝ (qPart w) x = ∑ b, w (.inr b) * x b := by
    simp [qPart, PiLp.inner_apply, mul_comm]
  rw [h1, map_sum, h2]
  simp [Complex.real_smul, ofReal_sum]

theorem fderiv_eq_of_annihilated : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 →
    ∀ f : Sch l, (∀ j : l, dRho (s *ᵥ Pi.single (.inl j) 1) f = I • dRho (s *ᵥ Pi.single (.inr j) 1) f) →
    ∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) =
      2 * π * I * ((-(Q * P⁻¹))ᵀ *ᵥ fun i => (x i : ℂ)) a * f x := by
  intro l _ _ s P Q hP hQ hdet f hf a x
  set u : l → ℂ := fun b => fderiv ℝ f x (EuclideanSpace.single b 1) with hu
  set xC : l → ℂ := fun i => (x i : ℂ) with hxC
  have hj : ∀ j, ∑ b, P b j * u b + 2 * π * I * (∑ b, Q b j * xC b) * f x = 0 := by
    intro j
    have e := congrArg (fun g : Sch l => g x) (hf j)
    simp only [SchwartzMap.smul_apply, smul_eq_mul, dRho_apply_basis] at e
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at e
    simp only [hP, hQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    simp only [hu, hxC]
    linear_combination e
  have hv : Pᵀ *ᵥ u = -(2 * π * I * f x) • (Qᵀ *ᵥ xC) := by
    funext j
    simp only [mulVec, dotProduct, transpose_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hj j
  have hunit : IsUnit Pᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
  have hu' : u = (Pᵀ)⁻¹ *ᵥ (Pᵀ *ᵥ u) := by rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  have key : u a = ((Pᵀ)⁻¹ *ᵥ (-(2 * π * I * f x) • (Qᵀ *ᵥ xC))) a := by rw [← hv, ← hu']
  change u a = _
  rw [key, mulVec_smul, mulVec_mulVec, ← transpose_nonsing_inv, ← transpose_mul, Matrix.transpose_neg,
    Matrix.neg_mulVec]
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end GlobalTheory.RealWeil
