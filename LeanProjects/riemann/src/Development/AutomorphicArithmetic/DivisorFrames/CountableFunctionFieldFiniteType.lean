import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry IsLocalRing GlobalTheory GlobalTheory.ValCount GlobalTheory.TrueGeo
open scoped Classical

theorem UpperTheory.countable_functionField_finiteType :
    ∀ (R : Type) [CommRing R] [Countable R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Spec (.of R)) [LocallyOfFiniteType p], Countable X.functionField := by
  intro R _ _ X _ p _
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hft : (p.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  haveI : Countable Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toEquiv.injective.countable
  haveI : Countable Γ(X, U) := by
    letI := (p.appLE ⊤ U le_top).hom.toAlgebra
    have h : Algebra.FiniteType Γ(Spec (.of R), ⊤) Γ(X, U) := hft
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
    haveI : Countable (MvPolynomial (Fin n) Γ(Spec (.of R), ⊤)) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine MvPolynomial.cardinalMk_le_max.trans ?_
      simp [Cardinal.mk_le_aleph0]
    exact hf.countable
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have hs : Function.Surjective (fun ab : Γ(X, U) × Γ(X, U) =>
      (algebraMap Γ(X, U) X.functionField ab.1 / algebraMap Γ(X, U) X.functionField ab.2)) := by
    intro z
    obtain ⟨a, b, -, h⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) z
    exact ⟨(a, b), h⟩
  exact hs.countable
