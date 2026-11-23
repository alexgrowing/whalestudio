import Development.EtaleCohomology.EtaleSheaves.LineOneCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChartsPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev D (i : Fin 2) : P1.Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

lemma X_mem (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℤ i)

lemma D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem i) one_pos

lemma D_cover : ⨆ i, D i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · exact fun i => ⟨1, X_mem i⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have h : Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) ≤
        (Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).restrictScalars ℤ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact h hx

end LateralTheory.E.ChartsPf
