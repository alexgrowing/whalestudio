import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_isChart : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by
  intro k _ G _ hG
  have hs : Smooth G.hom := hG.2.1
  let e : algOver k k ⟶ G := 1
  let x0 : (Sp k) := IsLocalRing.closedPoint k
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left) (x := e.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  have hft : Algebra.FiniteType k R := by
    have h1 : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h1
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hr : Set.range e.left ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    have : y = x0 := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]; exact hx
  let l : algOver k k ⟶ algOver k R := Over.homMk (IsOpenImmersion.lift i e.left hr) (by
    have := Over.w e
    rw [← this]
    show _ ≫ Spec.map φ = _
    rw [hφ, IsOpenImmersion.lift_fac_assoc])
  obtain ⟨ε, hε⟩ := algOverHom_surjective l
  obtain ⟨s, hsg⟩ := hft.out
  refine ⟨R, inferInstance, inferInstance, j, ε, s.card,
    fun n => (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n)), hi, ?_, ?_, ?_⟩
  · rw [hε]
    ext1
    exact IsOpenImmersion.lift_fac i e.left hr
  · rw [eq_top_iff, ← hsg, Algebra.adjoin_le_iff]
    intro a ha
    have h1 : a - algebraMap k R (ε a) ∈ Algebra.adjoin k (Set.range fun n =>
        (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n))) :=
      Algebra.subset_adjoin ⟨s.equivFin ⟨a, ha⟩, by simp⟩
    have h2 := add_mem h1 (Subalgebra.algebraMap_mem _ (ε a))
    simpa using h2
  · intro n
    simp

end GlobalTheory.SS.ArcInf
