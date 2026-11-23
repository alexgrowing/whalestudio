import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem UpperTheory.Cb.adjoin_degree_zero_variables_eq_top (N : ℕ) :
    Algebra.adjoin (↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
      (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0 :=
      MvPolynomial.isHomogeneous_C _ a
    exact Subalgebra.algebraMap_mem _ (⟨_, hC⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p i hp =>
    exact Subalgebra.mul_mem _ (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩)

private theorem UpperTheory.Cb.compactSpace_projective_space (N : ℕ) : CompactSpace (PSpace ℂ N) := by
  have hX : ∀ i : Fin (N + 1), (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 1 :=
    fun i => MvPolynomial.isHomogeneous_X ℂ i
  have hcov := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ) (fun i => ⟨1, hX i⟩)
    (UpperTheory.Cb.adjoin_degree_zero_variables_eq_top N)
  refine ⟨?_⟩
  have huniv : (Set.univ : Set (PSpace ℂ N)) =
      ⋃ i, ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
        (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) : (PSpace ℂ N).Opens) : Set (PSpace ℂ N)) := by
    have := congrArg (fun U : (PSpace ℂ N).Opens => (U : Set (PSpace ℂ N))) hcov
    simpa using this.symm
  rw [huniv]
  exact isCompact_iUnion fun i =>
    (Proj.isAffineOpen_basicOpen _ _ (hX i) Nat.one_pos).isCompact

theorem UpperTheory.Cb.compactSpace_of_projective_and_of_finite :
    (∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ), IsProjOver s → CompactSpace Z) ∧ ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z), IsFinite c → CompactSpace Z → CompactSpace Y := by
  refine ⟨?_, ?_⟩
  · rintro Z s ⟨N, i, hi, -⟩
    haveI := UpperTheory.Cb.compactSpace_projective_space N
    exact QuasiCompact.compactSpace_of_compactSpace i
  · intro Y Z c hc hZ
    exact QuasiCompact.compactSpace_of_compactSpace c
