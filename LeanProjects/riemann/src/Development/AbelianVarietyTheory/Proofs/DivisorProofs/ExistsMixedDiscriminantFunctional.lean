import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixPolar

variable {κ : Type} [Fintype κ] {D : ℕ}

theorem exists_functional (Q : MvPolynomial κ ℂ) (hQ : Q.IsHomogeneous D) :
    ∃ Λ : MvPolynomial κ ℝ →ₗ[ℝ] ℂ, ∀ n : κ → ℝ, Λ (lin n ^ D) = MvPolynomial.eval (fun i => (n i : ℂ)) Q := by
  refine ⟨∑ α ∈ Q.support, (MvPolynomial.lcoeff ℝ α).smulRight (Q.coeff α / (α.multinomial : ℂ)), fun n => ?_⟩
  have hl : lin n = ∑ i, n i • MvPolynomial.X i := by
    simp [lin, MvPolynomial.smul_eq_C_mul]
  rw [LinearMap.sum_apply, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : (α.sum fun _ m => m) = D := by
    have := hQ (MvPolynomial.mem_support_iff.1 hα)
    rw [← this, Finsupp.weight_apply]
    simp
  have hm : (α.multinomial : ℂ) ≠ 0 := by
    rw [Finsupp.multinomial_eq]
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  rw [LinearMap.smulRight_apply, MvPolynomial.lcoeff_apply, hl,
    MvPolynomial.coeff_linearCombination_X_pow_of_fintype, if_pos hd, Finsupp.prod_fintype _ _ (by simp),
    Complex.real_smul]
  push_cast
  field_simp

omit [Fintype κ] in

theorem adjugate_isHomogeneous (P : Matrix (Fin (D + 1)) (Fin (D + 1)) (MvPolynomial κ ℂ))
    (hP : ∀ i j, (P i j).IsHomogeneous 1) (i j : Fin (D + 1)) : (P.adjugate i j).IsHomogeneous D := by
  rw [adjugate_fin_succ_eq_det_submatrix, det_apply]
  have h₀ : ((-1 : MvPolynomial κ ℂ) ^ ((j : ℕ) + i)).IsHomogeneous 0 := by
    simpa using MvPolynomial.isHomogeneous_C κ ((-1 : ℂ) ^ ((j : ℕ) + i))
  have h₁ := h₀.mul (MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun s : Equiv.Perm (Fin D) => Equiv.Perm.sign s • ∏ t, P.submatrix j.succAbove i.succAbove (s t) t) D
    fun s _ => by
      have h := MvPolynomial.IsHomogeneous.prod Finset.univ
        (fun t => P.submatrix j.succAbove i.succAbove (s t) t) (fun _ => 1) fun t _ => hP _ _
      rw [Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one] at h
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with e | e
      · rw [e, one_smul]; exact h
      · rw [e, Units.neg_smul, one_smul]; exact h.neg)
  rwa [zero_add] at h₁

theorem exists_functional_mix : ∀ (κ : Type) [Fintype κ] (D : ℕ) (C : κ → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) (M : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ), ∃ Λ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ, ∀ n : κ → ℝ, Λ (lin n ^ D) = mix D (∑ i, (n i : ℂ) • C i) M := by
  intro κ _ D C M
  let P : Matrix (Fin (D + 1)) (Fin (D + 1)) (MvPolynomial κ ℂ) :=
    Matrix.of fun a b => ∑ i, MvPolynomial.X i * MvPolynomial.C (C i a b)
  have hP (a b : Fin (D + 1)) : (P a b).IsHomogeneous 1 :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ =>
      (MvPolynomial.isHomogeneous_X ℂ i).mul (MvPolynomial.isHomogeneous_C κ _)
  have hQ : (P.adjugate * M.map MvPolynomial.C).trace.IsHomogeneous D := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
    rw [diag_apply, Matrix.mul_apply]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ =>
      (adjugate_isHomogeneous P hP a b).mul (MvPolynomial.isHomogeneous_C κ (M b a))
  obtain ⟨Λ, hΛ⟩ := exists_functional _ hQ
  refine ⟨(D.factorial / Real.pi ^ (D + 1) : ℝ) • (Complex.reLm ∘ₗ Λ), fun n => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.comp_apply, hΛ, mix, smul_eq_mul, Complex.reLm_coe]
  congr 2
  have e : ∑ i, (n i : ℂ) • C i = (MvPolynomial.eval fun i => (n i : ℂ)).mapMatrix P := by
    ext a b
    simp [P, Matrix.sum_apply]
  rw [e, ← RingHom.map_adjugate]
  simp [trace, Matrix.mul_apply]

end GlobalTheory.MixPolar
