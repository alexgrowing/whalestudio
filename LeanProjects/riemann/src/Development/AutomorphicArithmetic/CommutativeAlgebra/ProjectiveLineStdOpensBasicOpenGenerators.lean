import Mathlib
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafCore

open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsMultivariableHensel

namespace UpperTheory.ProjectiveLineClosure

open GroundTheory.Arith.SchemeCoh ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem closure_chart (i j : Fin 2) (hij : i ≠ j) :
    Subring.closure {chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j)} = ⊤ := by
  have hiso : IsIso (Proj.awayToSection (grading ℤ 1) (MvPolynomial.X i)) := by
    rw [← Proj.basicOpenIsoAway_hom (grading ℤ 1) (MvPolynomial.X i) (X_mem i) one_pos]
    infer_instance
  have hsurj := (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grading ℤ 1) (MvPolynomial.X i))).2
  have hpoly : ∀ a : MvPolynomial (Fin (1 + 1)) ℤ,
      chartHom (A := ℤ) (n := 1) i a ∈ Subring.closure {chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j)} := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      rw [show (MvPolynomial.C c : MvPolynomial (Fin (1 + 1)) ℤ) = (c : MvPolynomial (Fin (1 + 1)) ℤ) from
        eq_intCast MvPolynomial.C c, map_intCast]
      exact intCast_mem _ c
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      by_cases hn : n = i
      · subst hn
        rw [chartHom_X_self]
        exact one_mem _
      · have hnj : n = j := by
          fin_cases n <;> fin_cases i <;> fin_cases j <;> simp_all
        subst hnj
        exact Subring.subset_closure rfl
  rw [eq_top_iff]
  intro s _
  obtain ⟨y, rfl⟩ := hsurj s
  obtain ⟨k, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem i) y
  have ha' : a ∈ grading ℤ 1 k := by simpa using ha
  convert hpoly a using 1
  exact (chartHom_of_mem i ha').symm

private theorem chartHom_eq_ratio (i j : Fin 2) :
    chartHom (A := ℤ) (n := 1) i (MvPolynomial.X j) =
      ProjTwist.ratio (grading ℤ 1) (X_mem i) (X_mem j) := by
  rw [chartHom_of_mem i (X_mem j)]
  unfold ProjTwist.ratio
  congr 1
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk]

private theorem mul_res :
    resR (inf_le_left : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 0)
        (chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1)) *
      resR (inf_le_right : stdOpen ℤ 1 0 ⊓ stdOpen ℤ 1 1 ≤ stdOpen ℤ 1 1)
        (chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0)) = 1 := by
  have h := ProjTwist.ratio_mul_ratio' (𝒜 := grading ℤ 1) (X_mem (A := ℤ) (n := 1) 0)
    (X_mem (A := ℤ) (n := 1) 1) (X_mem (A := ℤ) (n := 1) 0)
  rw [ProjTwist.ratio_self] at h
  rw [chartHom_eq_ratio, chartHom_eq_ratio, mul_comm]
  exact h.trans (map_one _)

end UpperTheory.ProjectiveLineClosure

open GroundTheory.Arith.SchemeCoh ProjSpace UpperTheory.ProjectiveLineClosure in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem UpperTheory.projectiveLine_std_opens_basicOpen_generators :
    ∃ (τ : Γ(P1, stdOpen 0)) (σ : Γ(P1, stdOpen 1)),
        IsAffineOpen (stdOpen 0) ∧ IsAffineOpen (stdOpen 1) ∧
        Subring.closure {τ} = ⊤ ∧ Subring.closure {σ} = ⊤ ∧
        P1.basicOpen τ = stdOpen 0 ⊓ stdOpen 1 ∧ P1.basicOpen σ = stdOpen 0 ⊓ stdOpen 1 ∧
        P1.presheaf.map (homOfLE (inf_le_left : stdOpen 0 ⊓ stdOpen 1 ≤ stdOpen 0)).op τ *
          P1.presheaf.map (homOfLE (inf_le_right : stdOpen 0 ⊓ stdOpen 1 ≤ stdOpen 1)).op σ = 1 := by
  refine ⟨chartHom (A := ℤ) (n := 1) 0 (MvPolynomial.X 1),
    chartHom (A := ℤ) (n := 1) 1 (MvPolynomial.X 0),
    isAffineOpen_stdOpen (A := ℤ) (n := 1) 0, isAffineOpen_stdOpen (A := ℤ) (n := 1) 1,
    closure_chart 0 1 (by decide), closure_chart 1 0 (by decide),
    basicOpen_chartHom_X (A := ℤ) (n := 1) 0 1, ?_, ?_⟩
  · refine (basicOpen_chartHom_X (A := ℤ) (n := 1) 1 0).trans ?_
    exact inf_comm _ _
  · exact mul_res
