import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4

theorem exists_map_const_eq_of_isAlgClosed {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [Field L] (i : Ω →+* L) (σ : L →+* L) (c : Ω) : ∃ c' : Ω, σ (i c) = i c' := by
  letI : Algebra Ω L := i.toAlgebra
  obtain ⟨p, hp, h0⟩ : IsIntegral ℚ c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  have e : (σ.comp i).comp (algebraMap ℚ Ω) = i.comp (algebraMap ℚ Ω) := RingHom.ext_rat _ _
  have hint : IsIntegral Ω (σ (i c)) := by
    refine ⟨p.map (algebraMap ℚ Ω), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    show p.eval₂ (i.comp (algebraMap ℚ Ω)) ((σ.comp i) c) = 0
    rw [← e, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c', hc'⟩ := minpoly.mem_range_of_degree_eq_one Ω (σ (i c))
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint))
  exact ⟨c', hc'.symm⟩

theorem isIntegral_map_of_map_range {R L : Type} [CommRing R] [Field L] [Algebra R L] (σ : L →+* L)
    (h : ∀ r : R, ∃ r' : R, σ (algebraMap R L r) = algebraMap R L r') {x : L} (hx : IsIntegral R x) :
    IsIntegral R (σ x) := by
  obtain ⟨p, hp, h0⟩ := hx
  have hl : p.map (σ.comp (algebraMap R L)) ∈ Polynomial.lifts (algebraMap R L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨r', hr'⟩ := h (p.coeff n)
    exact ⟨r', by rw [Polynomial.coeff_map, RingHom.comp_apply, hr']⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, h0, map_zero]

theorem map_mem_ringOfIntegers_of_fix_mdl :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (ε : Ω →+* ℂ)
      (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)),
      letI := GlobalTheory.K4.algPoly X Γ'
      letI := GlobalTheory.K4.algMdl X Γ' S
      ∀ (σ : GlobalTheory.K4.lev X Γ' ≃ₐ[GlobalTheory.K4.mdl X Γ' S] GlobalTheory.K4.lev X Γ') (x : GlobalTheory.K4.lev X Γ'),
        x ∈ FunctionField.ringOfIntegers Ω (GlobalTheory.K4.lev X Γ') →
          σ x ∈ FunctionField.ringOfIntegers Ω (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ _ _ ε X Γ' S
  letI := GlobalTheory.K4.algPoly X Γ'
  letI := GlobalTheory.K4.algMdl X Γ' S
  intro σ x hx
  have hj : σ ⟨X.jK, jK_mem_lev X Γ'⟩ = ⟨X.jK, jK_mem_lev X Γ'⟩ :=
    σ.commutes (⟨X.jK, jK_mem_mdl X Γ' S⟩ : mdl X Γ' S)
  have key : ∀ P : Polynomial Ω, ∃ Q : Polynomial Ω, σ (jPoly X Γ' P) = jPoly X Γ' Q := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P P' hP hP' =>
      obtain ⟨Q, hQ⟩ := hP
      obtain ⟨Q', hQ'⟩ := hP'
      exact ⟨Q + Q', by rw [map_add, map_add, hQ, hQ', map_add]⟩
    | monomial n c =>
      obtain ⟨c', hc'⟩ := exists_map_const_eq_of_isAlgClosed (levConst X Γ') (σ : lev X Γ' →+* lev X Γ') c
      refine ⟨Polynomial.monomial n c', ?_⟩
      simp only [jPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, map_mul, map_pow]
      rw [hj, ← hc']
      rfl
  exact isIntegral_map_of_map_range (R := Polynomial Ω) (σ : lev X Γ' →+* lev X Γ') key hx

end GlobalTheory.K4
