import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosed

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion
open Polynomial
open scoped IntermediateField

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign

private theorem sq_parts (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) :
    z.re ^ 2 - z.im ^ 2 = a ∧ z.re * z.im = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at h1 h2
  exact ⟨by linarith, by linarith⟩

private theorem conj_of_sq_nonneg (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) (ha : 0 ≤ a) :
    z = starRingEnd ℂ z := by
  obtain ⟨h1, h2⟩ := sq_parts z a h
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have him : z.im = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [h3] at h1
      nlinarith [sq_nonneg z.im]
    · exact h3
  exact (Complex.conj_eq_iff_im.mpr him).symm

private theorem conj_of_sq_nonpos (z : ℂ) (a : ℤ) (h : z ^ 2 = (a : ℂ)) (ha : a ≤ 0) :
    -z = starRingEnd ℂ z := by
  obtain ⟨h1, h2⟩ := sq_parts z a h
  have ha' : (a : ℝ) ≤ 0 := by exact_mod_cast ha
  have hre : z.re = 0 := by
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at h1
      nlinarith [sq_nonneg z.re]
  apply Complex.ext
  · simp [hre]
  · simp

end UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.mkQ :
    MkQ := by
  intro Y Ω _ _ _ _ _ _ x a hx ⟨g, hg⟩
  have hxa : x ^ 2 = algebraMap Y Ω (a : Y) := by rw [hx, map_intCast]
  have heval : aeval x (X ^ 2 - C (a : Y) : Y[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hxa, sub_self]
  have hint : IsIntegral Y x := ⟨X ^ 2 - C (a : Y), monic_X_pow_sub_C _ two_ne_zero, heval⟩
  have hirr : Irreducible (X ^ 2 - C (a : Y) : Y[X]) := by
    refine X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hg ?_)
    have h2 : x ^ 2 = (algebraMap Y Ω b) ^ 2 := by rw [hxa, ← map_pow, hb]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · rw [h]; exact g.commutes b
    · rw [h, map_neg]; congr 1; exact g.commutes b
  have hmin : minpoly Y x = X ^ 2 - C (a : Y) :=
    (minpoly.eq_of_irreducible_of_monic hirr heval (monic_X_pow_sub_C _ two_ne_zero)).symm
  have hdeg : (minpoly Y x).natDegree = 2 := by rw [hmin, natDegree_X_pow_sub_C]
  have hfin : Module.finrank Y Y⟮x⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField Y⟮x⟯ := NumberField.of_module_finite Y _
  have hconj : x ∈ GlobalTheory.CMSub.conjStable Ω := by
    have hφ : ∀ φ : Ω →+* ℂ, (φ x) ^ 2 = (a : ℂ) := fun φ => by rw [← map_pow, hx, map_intCast]
    rcases le_total 0 a with ha | ha
    · exact ⟨x, fun φ => UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign.conj_of_sq_nonneg _ a (hφ φ) ha⟩
    · exact ⟨-x, fun φ => by rw [map_neg]; exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.SquareConjugationSign.conj_of_sq_nonpos _ a (hφ φ) ha⟩
  have hle : Y⟮x⟯ ≤ GlobalTheory.CMSub.conjField Y Ω := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hconj
  have cm : IsCMField Y⟮x⟯ := GlobalTheory.CMSub.isCMField_of_le _ hle
  have hxK : x ∈ Y⟮x⟯ := IntermediateField.mem_adjoin_simple_self Y x
  have hspan : ∀ y : Y⟮x⟯, ∃ b c : Y, y = algebraMap Y Y⟮x⟯ b + algebraMap Y Y⟮x⟯ c * ⟨x, hxK⟩ := by
    intro y
    obtain ⟨f, hf, rfl⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval y
    rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have hf' : f = C (f.coeff 1) * X + C (f.coeff 0) := Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
    rw [hf', map_add, map_mul, aeval_C, aeval_C, aeval_X, IntermediateField.adjoin.powerBasis_gen, add_comm]
    simp only [coeff_add, coeff_C_mul, coeff_X_zero, coeff_X_one, coeff_C_zero, coeff_C_succ, mul_zero, mul_one, zero_add, add_zero]
    rfl
  refine ⟨⟨Y⟮x⟯, nf, cm, hfin⟩, hxK, hspan, ?_⟩
  intro F _ _ h hY hhx y
  obtain ⟨b, c, rfl⟩ := hspan y
  have hb : ∀ e : Y, h (algebraMap Y Ω e) = algebraMap Y Ω e := hY
  show h ((algebraMap Y Ω b) + (algebraMap Y Ω c) * x) = (algebraMap Y Ω b) + (algebraMap Y Ω c) * x
  rw [map_add, map_mul, hb, hb, hhx]
