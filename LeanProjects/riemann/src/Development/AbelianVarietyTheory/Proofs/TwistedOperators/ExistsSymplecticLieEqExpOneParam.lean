import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter

open scoped Matrix

noncomputable section

namespace GlobalTheory.SymplecticOneParam

variable {l : Type} [Fintype l] [DecidableEq l]

theorem eq_exp_of_continuous_oneParameter (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) (hc : Continuous g)
    (h0 : g 0 = 1) (hadd : ∀ s t, g (s + t) = g s * g t) :
    HasDerivAt g (deriv g 0) 0 ∧ ∀ t : ℝ, g t = NormedSpace.exp (t • deriv g 0) := by
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
  have hsm := GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (l ⊕ l) (l ⊕ l) ℝ) g hc h0 hadd
  have hdiff : Differentiable ℝ g := hsm.differentiable (by simp)
  set Z := deriv g 0 with hZ
  have hd0 : HasDerivAt g Z 0 := (hdiff 0).hasDerivAt
  have hdt : ∀ t, HasDerivAt g (g t * Z) t := by
    intro t
    have h1 : HasDerivAt (fun s => g (s - t)) Z t := by
      have h := hd0
      rw [← sub_self t] at h
      exact h.comp_sub_const t t
    have h2 := h1.const_mul (g t)
    have h3 : (fun s => g t * g (s - t)) = g := by
      funext s; rw [← hadd, add_sub_cancel]
    rwa [h3] at h2
  refine ⟨hd0, fun t => ?_⟩
  set h : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun s => g s * NormedSpace.exp (s • (-Z)) with hh
  have hderh : ∀ s, HasDerivAt h 0 s := by
    intro s
    have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Z) s
    have := (hdt s).fun_mul he
    have key : g s * Z * NormedSpace.exp (s • -Z) + g s * (-Z * NormedSpace.exp (s • -Z)) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    exact this.congr_deriv key
  have hconst : h t = h 0 := is_const_of_deriv_eq_zero (fun s => (hderh s).differentiableAt)
    (fun s => (hderh s).deriv) t 0
  have hh0 : h 0 = 1 := by simp [hh, h0]
  have hinv : NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  calc g t = g t * (NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z)) := by rw [hinv, mul_one]
    _ = h t * NormedSpace.exp (t • Z) := by rw [hh, mul_assoc]
    _ = NormedSpace.exp (t • Z) := by rw [hconst, hh0, one_mul]

theorem exists_mem_sp_eq_exp : ∀ (l : Type) [Fintype l] [DecidableEq l] (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ),
    Continuous g → g 0 = 1 →
    (∀ s t, g (s + t) = g s * g t) → (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ t : ℝ, g t = NormedSpace.exp (t • Z) := by
  intro l _ _ g hc h0 hadd hsym
  obtain ⟨hd, hexp⟩ := eq_exp_of_continuous_oneParameter g hc h0 hadd
  refine ⟨deriv g 0, ?_, hexp⟩
  set Z := deriv g 0 with hZ
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  let T : Matrix (l ⊕ l) (l ⊕ l) ℝ →L[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (l ⊕ l) (l ⊕ l) ℝ ℝ).toLinearMap
  have hT : HasDerivAt (fun t => (g t)ᵀ) Zᵀ 0 := T.hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const (Matrix.J l ℝ)).fun_mul hd
  have hconst : (fun t => (g t)ᵀ * Matrix.J l ℝ * g t) = fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.transpose_mem (hsym t)
    rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose] at this
    exact this
  rw [hconst] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) (Matrix.J l ℝ))
  rw [h0, Matrix.transpose_one, mul_one, one_mul, add_eq_zero_iff_eq_neg] at huniq
  show Z ∈ skewAdjointMatricesLieSubalgebra (Matrix.J l ℝ)
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
    Matrix.IsAdjointPair, huniq, mul_neg]

end GlobalTheory.SymplecticOneParam
