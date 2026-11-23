import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_common_field_of_point_eq : ∀ (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X), a (closedPoint K₁) = b (closedPoint K₂) → ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b := by
  intro X K₁ K₂ _ _ a b h
  obtain ⟨⟨x, f⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ X).symm.surjective a
  obtain ⟨⟨y, g⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₂ X).symm.surjective b
  have hxy : x = y := by
    have h1 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₁ X).apply_symm_apply ⟨x, f⟩)
    have h2 := congrArg Sigma.fst ((Scheme.SpecToEquivOfField K₂ X).apply_symm_apply ⟨y, g⟩)
    exact h1.symm.trans (h.trans h2)
  subst hxy
  letI : Algebra (X.residueField x) K₁ := f.hom.toAlgebra
  letI : Algebra (X.residueField x) K₂ := g.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) K₁ K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) K₁ K₂)
  letI : Field ((TensorProduct (X.residueField x) K₁ K₂) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(TensorProduct (X.residueField x) K₁ K₂) ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := X.residueField x) (A := K₁) (B := K₂)).toRingHom, ?_⟩
  change Spec.map _ ≫ Spec.map f ≫ X.fromSpecResidueField x = Spec.map _ ≫ Spec.map g ≫ X.fromSpecResidueField x
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext c
  change Ideal.Quotient.mk m (TensorProduct.tmul _ (algebraMap _ K₁ c) 1) = Ideal.Quotient.mk m (TensorProduct.tmul _ 1 (algebraMap _ K₂ c))
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.Mum
