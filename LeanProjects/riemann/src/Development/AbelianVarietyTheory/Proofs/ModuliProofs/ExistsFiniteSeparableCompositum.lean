import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_finite_separable_compositum (K K' k : Type) [Field K] [Field K'] [Field k] [Algebra K k]
    [FiniteDimensional K k] [Algebra.IsSeparable K k] (φ : K →+* K') :
    ∃ (k' : Type) (_ : Field k') (_ : Algebra K' k') (g : k →+* k'), FiniteDimensional K' k' ∧
      Algebra.IsSeparable K' k' ∧ g.comp (algebraMap K k) = (algebraMap K' k').comp φ := by
  let Ω := AlgebraicClosure K'
  let _ : Algebra K K' := φ.toAlgebra
  let σ : k →ₐ[K] Ω := IsAlgClosed.lift
  let bs := Module.finBasis K k
  let k' := IntermediateField.adjoin K' (Set.range fun i => σ (bs i))
  have sepσ : ∀ z : k, IsSeparable K' (σ z) := fun z =>
    ((Algebra.IsSeparable.isSeparable K z).map σ σ.injective).tower_top _
  have h₁ : FiniteDimensional K' k' :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact (sepσ _).isIntegral)
  have h₂ : Algebra.IsSeparable K' k' :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable _ _).2 (by rintro _ ⟨i, rfl⟩; exact sepσ _)
  have hmem : ∀ z : k, σ z ∈ k' := fun z => by
    rw [← bs.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply K K' Ω]
    exact mul_mem (k'.algebraMap_mem _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  refine ⟨k', inferInstance, inferInstance, σ.toRingHom.codRestrict k'.toSubring hmem, h₁, h₂, ?_⟩
  ext z
  exact σ.commutes z

theorem splitFibres_of_isGrpPullback : Out.GtBaseChangeSt → ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → (∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)) → (∀ x : X', ∃ (k : Type) (_ : Field k) (_ : Algebra (X'.residueField x) k), FiniteDimensional (X'.residueField x) k ∧ Algebra.IsSeparable (X'.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) k)) ≫ X'.fromSpecResidueField x)).obj G')) := by
  intro hB X X' f G _ G' _ φ hφ hS x'
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS (f x')
  obtain ⟨k', _, _, g, h₁, h₂, hg⟩ :=
    exists_finite_separable_compositum (X.residueField (f x')) (X'.residueField x') k (f.residueFieldMap x').hom
  refine ⟨k', inferInstance, inferInstance, h₁, h₂, ?_⟩
  have key : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) ≫
      X.fromSpecResidueField (f x') =
      (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x') k')) ≫ X'.fromSpecResidueField x') ≫ f := by
    have a₁ : spMap g ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) =
        spMap (algebraMap (X'.residueField x') k') ≫ Spec.map (f.residueFieldMap x') :=
      (spMap_comp _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp _ _))
    rw [← Category.assoc, a₁, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc]
  obtain ⟨S', -, -, -, -, hGt'⟩ := hB _ _ (spMap g) S _ hGt
  refine ⟨S', ?_⟩
  have : IsMonHom (pullCompIso (spMap g) (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (f x')) k)) ≫
      X.fromSpecResidueField (f x')) G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  have h₀ := isGt_of_iso (pullCompIso (spMap g) _ G).symm hGt'
  rw [key] at h₀
  have h₃ := isGt_of_iso (pullCompIso _ f G) h₀
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G f) hφ
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x') k')) ≫
      X'.fromSpecResidueField x')).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  exact isGt_of_iso ((Over.pullback _).mapIso e) h₃

end GlobalTheory
