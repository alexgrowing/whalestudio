import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemSpanOrderTwoRelationIffCoordsEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Mulvec
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsLinearEquivQuotientByOrderTwoCoords

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.algebraMap_signedInvolutionQuotientDet_mem_span :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z : MonoidAlgebra A Γ, algebraMap A (MonoidAlgebra A Γ) (detR c ε z) ∈ Ideal.span {rel A c ε, z} := by
  intro A _ Γ _ _ c ε h1 h2 h3 z
  obtain ⟨e, he⟩ := UpperTheory.V.B5.exists_linearEquiv_quotientByOrderTwo_coords (A := A) c ε h1 h2 h3
  have hsc : ∀ (d : A) (w : MonoidAlgebra A Γ),
      coord c ε (algebraMap A (MonoidAlgebra A Γ) d * w) = d • coord c ε w := by
    intro d w
    funext i
    simp [coord, Algebra.algebraMap_eq_smul_one]
    ring
  obtain ⟨y, hy⟩ := e.surjective ((mat c ε z).adjugate.mulVec (coord c ε 1))
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hu : coord c ε u = (mat c ε z).adjugate.mulVec (coord c ε 1) := by
    rw [← he]
    exact hy
  have hcoord : coord c ε (z * u) = coord c ε (algebraMap A _ (detR c ε z) * 1) := by
    rw [UpperTheory.V.B5.coords_mul_eq_quotientMatrix_mulVec c ε h1 h2 h3, hu, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hsc,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [mul_one] at hcoord
  have hcls : cls A c ε (algebraMap A _ (detR c ε z)) = cls A c ε (z * u) := by
    apply e.injective
    rw [he, he, hcoord]
  have hmem : algebraMap A _ (detR c ε z) - z * u ∈ Ideal.span {rel A c ε} :=
    Ideal.Quotient.eq.mp hcls
  have hsub : Ideal.span {rel A c ε} ≤ Ideal.span {rel A c ε, z} :=
    Ideal.span_mono (by simp)
  have hz : z * u ∈ Ideal.span {rel A c ε, z} :=
    Ideal.mul_mem_right u _ (Ideal.subset_span (by simp))
  have := Ideal.add_mem _ (hsub hmem) hz
  simpa using this
